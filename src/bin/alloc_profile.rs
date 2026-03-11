//! Allocation profiler: runs a corpus workload with a size-bucketed counting
//! allocator to understand allocation patterns.

use rwlog::perf_corpus::{get_case, prepare_case, run_prepared};
use std::alloc::{GlobalAlloc, Layout};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

// Size buckets: 0-16, 17-32, 33-64, 65-128, 129-256, 257-512, 513-1024, 1025-4096, 4097+
const NUM_BUCKETS: usize = 9;

macro_rules! atomic_u64_array {
    ($n:expr) => {
        [const { AtomicU64::new(0) }; $n]
    };
}

static BUCKET_ALLOC_COUNTS: [AtomicU64; NUM_BUCKETS] = atomic_u64_array!(NUM_BUCKETS);
static BUCKET_ALLOC_BYTES: [AtomicU64; NUM_BUCKETS] = atomic_u64_array!(NUM_BUCKETS);
static BUCKET_DEALLOC_COUNTS: [AtomicU64; NUM_BUCKETS] = atomic_u64_array!(NUM_BUCKETS);
static TRACKING: AtomicBool = AtomicBool::new(false);

struct BucketAlloc;

static INNER: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn bucket_index(size: usize) -> usize {
    match size {
        0..=16 => 0,
        17..=32 => 1,
        33..=64 => 2,
        65..=128 => 3,
        129..=256 => 4,
        257..=512 => 5,
        513..=1024 => 6,
        1025..=4096 => 7,
        _ => 8,
    }
}

fn bucket_label(i: usize) -> &'static str {
    match i {
        0 => "0-16",
        1 => "17-32",
        2 => "33-64",
        3 => "65-128",
        4 => "129-256",
        5 => "257-512",
        6 => "513-1024",
        7 => "1025-4096",
        8 => "4097+",
        _ => unreachable!(),
    }
}

#[global_allocator]
static GLOBAL: BucketAlloc = BucketAlloc;

unsafe impl GlobalAlloc for BucketAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if TRACKING.load(Ordering::Relaxed) {
            let idx = bucket_index(layout.size());
            BUCKET_ALLOC_COUNTS[idx].fetch_add(1, Ordering::Relaxed);
            BUCKET_ALLOC_BYTES[idx].fetch_add(layout.size() as u64, Ordering::Relaxed);
        }
        unsafe { INNER.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if TRACKING.load(Ordering::Relaxed) {
            let idx = bucket_index(layout.size());
            BUCKET_DEALLOC_COUNTS[idx].fetch_add(1, Ordering::Relaxed);
        }
        unsafe { INNER.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if TRACKING.load(Ordering::Relaxed) {
            // Count as dealloc of old + alloc of new
            let old_idx = bucket_index(layout.size());
            BUCKET_DEALLOC_COUNTS[old_idx].fetch_add(1, Ordering::Relaxed);
            let new_idx = bucket_index(new_size);
            BUCKET_ALLOC_COUNTS[new_idx].fetch_add(1, Ordering::Relaxed);
            BUCKET_ALLOC_BYTES[new_idx].fetch_add(new_size as u64, Ordering::Relaxed);
        }
        unsafe { INNER.realloc(ptr, layout, new_size) }
    }
}

fn reset_buckets() {
    for i in 0..NUM_BUCKETS {
        BUCKET_ALLOC_COUNTS[i].store(0, Ordering::Relaxed);
        BUCKET_ALLOC_BYTES[i].store(0, Ordering::Relaxed);
        BUCKET_DEALLOC_COUNTS[i].store(0, Ordering::Relaxed);
    }
}

fn print_buckets() {
    let mut total_allocs = 0u64;
    let mut total_bytes = 0u64;
    let mut total_deallocs = 0u64;

    println!(
        "{:<12} {:>12} {:>12} {:>12} {:>12}",
        "Size Range", "Allocs", "Bytes", "Deallocs", "Net Allocs"
    );
    println!("{}", "-".repeat(60));

    for i in 0..NUM_BUCKETS {
        let count = BUCKET_ALLOC_COUNTS[i].load(Ordering::Relaxed);
        let bytes = BUCKET_ALLOC_BYTES[i].load(Ordering::Relaxed);
        let deallocs = BUCKET_DEALLOC_COUNTS[i].load(Ordering::Relaxed);
        total_allocs += count;
        total_bytes += bytes;
        total_deallocs += deallocs;
        if count > 0 || deallocs > 0 {
            println!(
                "{:<12} {:>12} {:>12} {:>12} {:>12}",
                bucket_label(i),
                count,
                bytes,
                deallocs,
                count as i64 - deallocs as i64
            );
        }
    }
    println!("{}", "-".repeat(60));
    println!(
        "{:<12} {:>12} {:>12} {:>12} {:>12}",
        "TOTAL",
        total_allocs,
        total_bytes,
        total_deallocs,
        total_allocs as i64 - total_deallocs as i64
    );
    if total_allocs > 0 {
        println!(
            "\nAvg alloc size: {:.1} bytes",
            total_bytes as f64 / total_allocs as f64
        );
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let case_id = args
        .iter()
        .position(|a| a == "--id")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str())
        .unwrap_or("recursive_even_backward_first64");
    let iters: usize = args
        .iter()
        .position(|a| a == "--iters")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(3);

    let case = get_case(case_id);

    println!("=== Allocation Profile for '{}' ===\n", case_id);

    // Warmup (not tracked)
    {
        let prepared = prepare_case(&case);
        let _ = run_prepared(&case, prepared);
    }

    // Tracked runs
    for run in 0..iters {
        reset_buckets();
        let prepared = prepare_case(&case);
        TRACKING.store(true, Ordering::SeqCst);
        let n = run_prepared(&case, prepared);
        TRACKING.store(false, Ordering::SeqCst);
        println!("--- Run {} ({} answers) ---", run + 1, n);
        print_buckets();
        println!();
    }
}

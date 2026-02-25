//! Reports sizes of all key data structures for allocation analysis.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rwlog::chr;
use rwlog::drop_fresh;
use rwlog::factors;
use rwlog::nf;
use rwlog::node;
use rwlog::rel;
use rwlog::work::{self, CallKey, ComposeWork, Env, FixWork, MeetWork, PipeWork, Table, Tables};
use std::mem::size_of;

// The concrete constraint type used in perf benchmarks
type C = chr::ChrState;

fn main() {
    println!("=== Data Structure Sizes (with ChrState constraint) ===\n");

    println!("--- Atomic Types ---");
    println!(
        "  TermId:            {:>4} bytes",
        size_of::<rwlog::term::TermId>()
    );
    println!(
        "  Term:              {:>4} bytes",
        size_of::<rwlog::term::Term>()
    );
    println!(
        "  FuncId:            {:>4} bytes",
        size_of::<rwlog::symbol::FuncId>()
    );
    println!(
        "  RelId:             {:>4} bytes",
        size_of::<rwlog::rel::RelId>()
    );
    println!("  ChrState:          {:>4} bytes", size_of::<C>());

    println!("\n--- NF & Related ---");
    println!("  NF<C>:             {:>4} bytes", size_of::<nf::NF<C>>());
    println!("  NF<()>:            {:>4} bytes", size_of::<nf::NF<()>>());
    println!(
        "  DropFresh<C>:      {:>4} bytes",
        size_of::<drop_fresh::DropFresh<C>>()
    );
    println!(
        "  DropFresh<()>:     {:>4} bytes",
        size_of::<drop_fresh::DropFresh<()>>()
    );
    println!("  RwT<C>:            {:>4} bytes", size_of::<nf::RwT<C>>());

    println!("\n--- Rel ---");
    println!("  Rel<C>:            {:>4} bytes", size_of::<rel::Rel<C>>());

    println!("\n--- Node ---");
    println!(
        "  Node<C>:           {:>4} bytes",
        size_of::<node::Node<C>>()
    );
    println!(
        "  NodeStep<C>:       {:>4} bytes",
        size_of::<node::NodeStep<C>>()
    );

    println!("\n--- Work Enum ---");
    println!(
        "  Work<C>:           {:>4} bytes",
        size_of::<work::Work<C>>()
    );
    println!(
        "  WorkStep<C>:       {:>4} bytes",
        size_of::<work::WorkStep<C>>()
    );

    println!("\n--- Work Variants ---");
    println!("  PipeWork<C>:       {:>4} bytes", size_of::<PipeWork<C>>());
    println!("  FixWork<C>:        {:>4} bytes", size_of::<FixWork<C>>());
    println!("  MeetWork<C>:       {:>4} bytes", size_of::<MeetWork<C>>());
    println!(
        "  ComposeWork<C>:    {:>4} bytes",
        size_of::<ComposeWork<C>>()
    );

    println!("\n--- Factors ---");
    println!(
        "  Factors<C>:        {:>4} bytes",
        size_of::<factors::Factors<C>>()
    );
    println!(
        "  Slice<C>:          {:>4} bytes",
        size_of::<factors::Slice<C>>()
    );

    println!("\n--- Fix/Tabling ---");
    println!("  CallKey<C>:        {:>4} bytes", size_of::<CallKey<C>>());
    println!("  Env<C>:            {:>4} bytes", size_of::<Env<C>>());
    println!("  Tables<C>:         {:>4} bytes", size_of::<Tables<C>>());
    println!("  Table<C>:          {:>4} bytes", size_of::<Table<C>>());

    println!("\n--- SmallVec Inline Sizes ---");
    println!(
        "  SmallVec<[TermId;1]>:   {:>4} bytes",
        size_of::<smallvec::SmallVec<[rwlog::term::TermId; 1]>>()
    );
    println!(
        "  SmallVec<[TermId;4]>:   {:>4} bytes",
        size_of::<smallvec::SmallVec<[rwlog::term::TermId; 4]>>()
    );
    println!(
        "  SmallVec<[(u32,u32);4]>:{:>4} bytes",
        size_of::<smallvec::SmallVec<[(u32, u32); 4]>>()
    );
    println!(
        "  SmallVec<[Slice;4]>:    {:>4} bytes",
        size_of::<smallvec::SmallVec<[factors::Slice<C>; 4]>>()
    );

    println!("\n--- Box/Arc Wrappers ---");
    println!(
        "  Box<Work<C>>:      {:>4} bytes (heap: {})",
        size_of::<Box<work::Work<C>>>(),
        size_of::<work::Work<C>>()
    );
    println!(
        "  Box<Node<C>>:      {:>4} bytes (heap: {})",
        size_of::<Box<node::Node<C>>>(),
        size_of::<node::Node<C>>()
    );
    println!(
        "  Arc<NF<C>>:        {:>4} bytes (heap: ~{})",
        size_of::<std::sync::Arc<nf::NF<C>>>(),
        size_of::<nf::NF<C>>() + 16
    );
    println!(
        "  Arc<CallKey<C>>:   {:>4} bytes (heap: ~{})",
        size_of::<std::sync::Arc<CallKey<C>>>(),
        size_of::<CallKey<C>>() + 16
    );

    println!("\n--- ChrState Internals ---");
    println!(
        "  ChrStore:          {:>4} bytes",
        size_of::<chr::ChrStore>()
    );
    println!(
        "  TokenStore:        {:>4} bytes",
        size_of::<chr::TokenStore>()
    );
    println!(
        "  VecDeque<u32>:     {:>4} bytes",
        size_of::<std::collections::VecDeque<u32>>()
    );
    println!(
        "  Arc<ChrProgram>:   {:>4} bytes",
        size_of::<std::sync::Arc<chr::ChrProgram>>()
    );

    // CallMode is not re-exported, skip it

    println!("\n--- Size Chain (why Work is 624 bytes) ---");
    println!("  ChrState:          {:>4} B", size_of::<C>());
    println!(
        "  DropFresh<C>:      {:>4} B (contains ChrState: {}B + map: {}B + 2×u32)",
        size_of::<drop_fresh::DropFresh<C>>(),
        size_of::<C>(),
        size_of::<smallvec::SmallVec<[(u32, u32); 4]>>()
    );
    println!(
        "  NF<C>:             {:>4} B (2× SmallVec<[TermId;1]>: {}B + DropFresh: {}B)",
        size_of::<nf::NF<C>>(),
        size_of::<smallvec::SmallVec<[rwlog::term::TermId; 1]>>(),
        size_of::<drop_fresh::DropFresh<C>>()
    );
    println!(
        "  Option<NF<C>>:     {:>4} B",
        size_of::<Option<nf::NF<C>>>()
    );
    println!(
        "  PipeWork<C>:       {:>4} B (2× Option<NF<C>>: {}B + Factors: {}B + ...)",
        size_of::<PipeWork<C>>(),
        size_of::<Option<nf::NF<C>>>() * 2,
        size_of::<factors::Factors<C>>()
    );
    println!(
        "  Work<C>:           {:>4} B (sized to ComposeWork; PipeWork boxed)",
        size_of::<work::Work<C>>()
    );
    println!(
        "  Box<Work<C>>:      {:>4} B on stack, {:>4} B heap alloc",
        size_of::<Box<work::Work<C>>>(),
        size_of::<work::Work<C>>()
    );

    println!("\n--- Key Sizes for Allocation Buckets ---");
    let work_size = size_of::<work::Work<C>>();
    let node_size = size_of::<node::Node<C>>();
    let nf_size = size_of::<nf::NF<C>>();
    println!("  Box<Work> heap allocation: {} bytes", work_size);
    println!("  Box<Node> heap allocation: {} bytes", node_size);
    println!("  NF<C> (inline, not boxed): {} bytes", nf_size);
    println!("\n  Allocation bucket mapping:");
    println!(
        "    129-256 range could be: Node<C> ({}) or NF<C> ({})?",
        node_size, nf_size
    );
    println!(
        "    513-1024 range could be: Work<C> ({}) or PipeWork<C> ({})?",
        work_size,
        size_of::<PipeWork<C>>()
    );
}

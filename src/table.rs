use dashmap::DashSet;
use parking_lot::Mutex;
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::goal::RelId;
use crate::nf::NF;
use crate::task::{Kont, TaskId};

/// A subscriber waiting for answers from a relation.
#[derive(Debug, Clone)]
pub struct Subscriber<C: Clone> {
    /// The task that is waiting.
    pub task_id: TaskId,
    /// The continuation to apply when answers arrive.
    pub kont: Kont<C>,
    /// Input NF to compose answers with.
    pub input: NF<C>,
}

/// A table tracking answers and subscribers for a single relation.
pub struct RelTable<C: Clone + Eq + Hash + Send + Sync + 'static> {
    /// Deduplicated answers.
    answers: DashSet<NF<C>>,
    /// Tasks waiting for answers.
    subscribers: Mutex<Vec<Subscriber<C>>>,
    /// Whether evaluation of this relation has started.
    started: AtomicBool,
    /// The relation's name (for debugging).
    name: String,
}

impl<C: Clone + Default + Eq + Hash + Send + Sync + 'static> RelTable<C> {
    /// Create a new relation table.
    pub fn new(name: &str) -> Self {
        Self {
            answers: DashSet::new(),
            subscribers: Mutex::new(Vec::new()),
            started: AtomicBool::new(false),
            name: name.to_string(),
        }
    }

    /// Check if evaluation has started.
    pub fn is_started(&self) -> bool {
        self.started.load(Ordering::SeqCst)
    }

    /// Mark the relation as started. Returns true if this call started it.
    pub fn start(&self) -> bool {
        !self.started.swap(true, Ordering::SeqCst)
    }

    /// Get the number of answers.
    pub fn answer_count(&self) -> usize {
        self.answers.len()
    }

    /// Get the number of subscribers.
    pub fn subscriber_count(&self) -> usize {
        self.subscribers.lock().len()
    }

    /// Add an answer to the table.
    ///
    /// Returns true if the answer was new (not already present).
    pub fn add_answer(&self, answer: NF<C>) -> bool {
        self.answers.insert(answer)
    }

    /// Check if an answer is already known.
    pub fn has_answer(&self, answer: &NF<C>) -> bool {
        self.answers.contains(answer)
    }

    /// Get all current answers.
    pub fn get_answers(&self) -> Vec<NF<C>> {
        self.answers.iter().map(|r| r.clone()).collect()
    }

    /// Add a subscriber.
    pub fn subscribe(&self, subscriber: Subscriber<C>) {
        self.subscribers.lock().push(subscriber);
    }

    /// Get all current subscribers.
    pub fn get_subscribers(&self) -> Vec<Subscriber<C>> {
        self.subscribers.lock().clone()
    }

    /// Clear subscribers (after notifying them).
    pub fn clear_subscribers(&self) {
        self.subscribers.lock().clear();
    }

    /// Get the relation name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Reset the table (for testing).
    pub fn reset(&self) {
        self.answers.clear();
        self.subscribers.lock().clear();
        self.started.store(false, Ordering::SeqCst);
    }
}

/// Manager for all relation tables.
pub struct TableStore<C: Clone + Default + Eq + Hash + Send + Sync + 'static> {
    tables: HashMap<RelId, RelTable<C>>,
}

impl<C: Clone + Default + Eq + Hash + Send + Sync + 'static> TableStore<C> {
    /// Create a new table store.
    pub fn new() -> Self {
        Self {
            tables: HashMap::new(),
        }
    }

    /// Register a new relation.
    pub fn register(&mut self, rel_id: RelId, name: &str) {
        self.tables.insert(rel_id, RelTable::new(name));
    }

    /// Get a table by relation ID.
    pub fn get(&self, rel_id: RelId) -> Option<&RelTable<C>> {
        self.tables.get(&rel_id)
    }

    /// Check if a relation is registered.
    pub fn is_registered(&self, rel_id: RelId) -> bool {
        self.tables.contains_key(&rel_id)
    }

    /// Number of registered relations.
    pub fn len(&self) -> usize {
        self.tables.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.tables.is_empty()
    }

    /// Iterator over all tables.
    pub fn iter(&self) -> impl Iterator<Item = (RelId, &RelTable<C>)> {
        self.tables.iter().map(|(&id, table)| (id, table))
    }

    /// Add an answer to a relation's table.
    ///
    /// Returns true if the answer was new.
    pub fn add_answer(&self, rel_id: RelId, answer: NF<C>) -> bool {
        if let Some(table) = self.tables.get(&rel_id) {
            table.add_answer(answer)
        } else {
            false
        }
    }

    /// Subscribe a task to a relation.
    pub fn subscribe(&self, rel_id: RelId, subscriber: Subscriber<C>) {
        if let Some(table) = self.tables.get(&rel_id) {
            table.subscribe(subscriber);
        }
    }

    /// Start a relation. Returns true if this call started it.
    pub fn start(&self, rel_id: RelId) -> bool {
        if let Some(table) = self.tables.get(&rel_id) {
            table.start()
        } else {
            false
        }
    }

    /// Check if a relation has started.
    pub fn is_started(&self, rel_id: RelId) -> bool {
        if let Some(table) = self.tables.get(&rel_id) {
            table.is_started()
        } else {
            false
        }
    }

    /// Get answers for a relation.
    pub fn get_answers(&self, rel_id: RelId) -> Vec<NF<C>> {
        if let Some(table) = self.tables.get(&rel_id) {
            table.get_answers()
        } else {
            Vec::new()
        }
    }

    /// Get subscribers for a relation.
    pub fn get_subscribers(&self, rel_id: RelId) -> Vec<Subscriber<C>> {
        if let Some(table) = self.tables.get(&rel_id) {
            table.get_subscribers()
        } else {
            Vec::new()
        }
    }
}

impl<C: Clone + Default + Eq + Hash + Send + Sync + 'static> Default for TableStore<C> {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of processing a Call goal.
#[derive(Debug)]
pub enum CallResult<C> {
    /// Relation not yet started - start it and block.
    StartAndBlock,
    /// Relation already started - replay answers and block.
    ReplayAndBlock(Vec<NF<C>>),
}

/// Notification when a new answer is produced.
#[derive(Debug, Clone)]
pub struct AnswerNotification<C: Clone> {
    /// The relation that produced the answer.
    pub rel_id: RelId,
    /// The new answer.
    pub answer: NF<C>,
    /// Subscribers to notify.
    pub subscribers: Vec<Subscriber<C>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::Wire;
    use smallvec::smallvec;

    fn make_identity_nf() -> NF<()> {
        NF::new(smallvec![], Wire::identity(0), smallvec![])
    }

    fn make_simple_nf(var: u32) -> NF<()> {
        NF::new(smallvec![], Wire::identity(var), smallvec![])
    }

    fn make_subscriber(task_id: TaskId) -> Subscriber<()> {
        Subscriber {
            task_id,
            kont: Kont::AltNext { remaining: smallvec![] },
            input: make_identity_nf(),
        }
    }

    // ========== REL TABLE TESTS ==========

    #[test]
    fn rel_table_new() {
        let table: RelTable<()> = RelTable::new("test");
        assert_eq!(table.name(), "test");
        assert!(!table.is_started());
        assert_eq!(table.answer_count(), 0);
        assert_eq!(table.subscriber_count(), 0);
    }

    #[test]
    fn rel_table_start() {
        let table: RelTable<()> = RelTable::new("test");
        assert!(!table.is_started());

        // First start returns true
        assert!(table.start());
        assert!(table.is_started());

        // Second start returns false
        assert!(!table.start());
        assert!(table.is_started());
    }

    #[test]
    fn rel_table_add_answer() {
        let table: RelTable<()> = RelTable::new("test");

        let nf = make_identity_nf();
        assert!(table.add_answer(nf.clone()));
        assert_eq!(table.answer_count(), 1);

        // Adding same answer returns false (already present)
        assert!(!table.add_answer(nf.clone()));
        assert_eq!(table.answer_count(), 1);
    }

    #[test]
    fn rel_table_add_different_answers() {
        let table: RelTable<()> = RelTable::new("test");

        let nf1 = make_identity_nf();
        let nf2 = make_simple_nf(1);

        assert!(table.add_answer(nf1));
        assert!(table.add_answer(nf2));
        assert_eq!(table.answer_count(), 2);
    }

    #[test]
    fn rel_table_has_answer() {
        let table: RelTable<()> = RelTable::new("test");

        let nf = make_identity_nf();
        assert!(!table.has_answer(&nf));

        table.add_answer(nf.clone());
        assert!(table.has_answer(&nf));
    }

    #[test]
    fn rel_table_get_answers() {
        let table: RelTable<()> = RelTable::new("test");

        let nf1 = make_identity_nf();
        let nf2 = make_simple_nf(1);

        table.add_answer(nf1.clone());
        table.add_answer(nf2.clone());

        let answers = table.get_answers();
        assert_eq!(answers.len(), 2);
    }

    #[test]
    fn rel_table_subscribe() {
        let table: RelTable<()> = RelTable::new("test");

        let sub1 = make_subscriber(0);
        let sub2 = make_subscriber(1);

        table.subscribe(sub1);
        table.subscribe(sub2);

        assert_eq!(table.subscriber_count(), 2);
    }

    #[test]
    fn rel_table_get_subscribers() {
        let table: RelTable<()> = RelTable::new("test");

        let sub = make_subscriber(42);
        table.subscribe(sub);

        let subs = table.get_subscribers();
        assert_eq!(subs.len(), 1);
        assert_eq!(subs[0].task_id, 42);
    }

    #[test]
    fn rel_table_clear_subscribers() {
        let table: RelTable<()> = RelTable::new("test");

        table.subscribe(make_subscriber(0));
        table.subscribe(make_subscriber(1));
        assert_eq!(table.subscriber_count(), 2);

        table.clear_subscribers();
        assert_eq!(table.subscriber_count(), 0);
    }

    #[test]
    fn rel_table_reset() {
        let table: RelTable<()> = RelTable::new("test");

        table.start();
        table.add_answer(make_identity_nf());
        table.subscribe(make_subscriber(0));

        assert!(table.is_started());
        assert_eq!(table.answer_count(), 1);
        assert_eq!(table.subscriber_count(), 1);

        table.reset();

        assert!(!table.is_started());
        assert_eq!(table.answer_count(), 0);
        assert_eq!(table.subscriber_count(), 0);
    }

    // ========== TABLE STORE TESTS ==========

    #[test]
    fn table_store_new() {
        let store: TableStore<()> = TableStore::new();
        assert!(store.is_empty());
        assert_eq!(store.len(), 0);
    }

    #[test]
    fn table_store_register() {
        let mut store: TableStore<()> = TableStore::new();
        store.register(0, "append");
        store.register(1, "reverse");

        assert_eq!(store.len(), 2);
        assert!(store.is_registered(0));
        assert!(store.is_registered(1));
        assert!(!store.is_registered(2));
    }

    #[test]
    fn table_store_get() {
        let mut store: TableStore<()> = TableStore::new();
        store.register(0, "test");

        let table = store.get(0);
        assert!(table.is_some());
        assert_eq!(table.unwrap().name(), "test");

        assert!(store.get(99).is_none());
    }

    #[test]
    fn table_store_add_answer() {
        let mut store: TableStore<()> = TableStore::new();
        store.register(0, "test");

        let nf = make_identity_nf();
        assert!(store.add_answer(0, nf.clone()));
        assert!(!store.add_answer(0, nf)); // Already present

        // Unregistered relation
        assert!(!store.add_answer(99, make_identity_nf()));
    }

    #[test]
    fn table_store_subscribe() {
        let mut store: TableStore<()> = TableStore::new();
        store.register(0, "test");

        store.subscribe(0, make_subscriber(1));
        store.subscribe(0, make_subscriber(2));

        let subs = store.get_subscribers(0);
        assert_eq!(subs.len(), 2);
    }

    #[test]
    fn table_store_start() {
        let mut store: TableStore<()> = TableStore::new();
        store.register(0, "test");

        assert!(!store.is_started(0));
        assert!(store.start(0));
        assert!(store.is_started(0));
        assert!(!store.start(0)); // Already started

        // Unregistered relation
        assert!(!store.start(99));
        assert!(!store.is_started(99));
    }

    #[test]
    fn table_store_get_answers() {
        let mut store: TableStore<()> = TableStore::new();
        store.register(0, "test");

        store.add_answer(0, make_identity_nf());
        store.add_answer(0, make_simple_nf(1));

        let answers = store.get_answers(0);
        assert_eq!(answers.len(), 2);

        // Unregistered relation
        assert!(store.get_answers(99).is_empty());
    }

    #[test]
    fn table_store_get_subscribers_unregistered() {
        let store: TableStore<()> = TableStore::new();
        assert!(store.get_subscribers(0).is_empty());
    }

    #[test]
    fn table_store_iter() {
        let mut store: TableStore<()> = TableStore::new();
        store.register(0, "a");
        store.register(1, "b");
        store.register(2, "c");

        let items: Vec<_> = store.iter().collect();
        assert_eq!(items.len(), 3);
    }

    // ========== SUBSCRIBER TESTS ==========

    #[test]
    fn subscriber_creation() {
        let sub: Subscriber<()> = Subscriber {
            task_id: 42,
            kont: Kont::FixFrame {
                rel_id: 0,
                body: 0,
                fix_goal: 0,
            },
            input: make_identity_nf(),
        };

        assert_eq!(sub.task_id, 42);
    }

    #[test]
    fn subscriber_clone() {
        let sub1 = make_subscriber(1);
        let sub2 = sub1.clone();

        assert_eq!(sub1.task_id, sub2.task_id);
    }

    // ========== CONCURRENT TESTS ==========

    #[test]
    fn concurrent_add_answers() {
        use std::thread;

        let table: RelTable<()> = RelTable::new("test");
        let table = std::sync::Arc::new(table);

        let handles: Vec<_> = (0..10)
            .map(|i| {
                let table = std::sync::Arc::clone(&table);
                thread::spawn(move || {
                    let nf = make_simple_nf(i);
                    table.add_answer(nf)
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        // All unique NFs should be added
        assert_eq!(table.answer_count(), 10);
    }

    #[test]
    fn concurrent_subscribe() {
        use std::thread;

        let table: RelTable<()> = RelTable::new("test");
        let table = std::sync::Arc::new(table);

        let handles: Vec<_> = (0..10)
            .map(|i| {
                let table = std::sync::Arc::clone(&table);
                thread::spawn(move || {
                    table.subscribe(make_subscriber(i as TaskId));
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(table.subscriber_count(), 10);
    }

    #[test]
    fn concurrent_start() {
        use std::thread;
        use std::sync::atomic::AtomicUsize;

        let table: RelTable<()> = RelTable::new("test");
        let table = std::sync::Arc::new(table);
        let start_count = std::sync::Arc::new(AtomicUsize::new(0));

        let handles: Vec<_> = (0..10)
            .map(|_| {
                let table = std::sync::Arc::clone(&table);
                let start_count = std::sync::Arc::clone(&start_count);
                thread::spawn(move || {
                    if table.start() {
                        start_count.fetch_add(1, Ordering::SeqCst);
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        // Only one thread should have successfully started it
        assert_eq!(start_count.load(Ordering::SeqCst), 1);
        assert!(table.is_started());
    }

    // ========== ANSWER NOTIFICATION TESTS ==========

    #[test]
    fn answer_notification_creation() {
        let notification: AnswerNotification<()> = AnswerNotification {
            rel_id: 0,
            answer: make_identity_nf(),
            subscribers: vec![make_subscriber(1), make_subscriber(2)],
        };

        assert_eq!(notification.rel_id, 0);
        assert_eq!(notification.subscribers.len(), 2);
    }

    // ========== COMPLEX SCENARIOS ==========

    #[test]
    fn simulate_tabling_workflow() {
        let mut store: TableStore<()> = TableStore::new();
        store.register(0, "append");

        // Task 1 calls append (first caller)
        assert!(!store.is_started(0));
        assert!(store.start(0)); // Returns true - this call started it

        // Task 1 starts evaluating append body...

        // Task 2 calls append (subscriber)
        store.subscribe(0, make_subscriber(2));

        // Task 1 produces an answer
        let answer1 = make_identity_nf();
        assert!(store.add_answer(0, answer1.clone())); // New answer

        // Get subscribers to notify
        let subs = store.get_subscribers(0);
        assert_eq!(subs.len(), 1);
        assert_eq!(subs[0].task_id, 2);

        // Task 2 receives answer1 and starts processing...

        // Task 3 calls append (gets existing answers)
        store.subscribe(0, make_subscriber(3));
        let existing = store.get_answers(0);
        assert_eq!(existing.len(), 1);

        // Task 1 produces another answer
        let answer2 = make_simple_nf(1);
        assert!(store.add_answer(0, answer2.clone()));

        // Get all subscribers for new answer
        let subs = store.get_subscribers(0);
        assert_eq!(subs.len(), 2); // Tasks 2 and 3
    }

    #[test]
    fn deduplication_prevents_infinite_loops() {
        let mut store: TableStore<()> = TableStore::new();
        store.register(0, "append");

        let answer = make_identity_nf();

        // First addition is new
        assert!(store.add_answer(0, answer.clone()));

        // Subsequent additions are duplicates
        assert!(!store.add_answer(0, answer.clone()));
        assert!(!store.add_answer(0, answer.clone()));
        assert!(!store.add_answer(0, answer.clone()));

        // Only one answer stored
        assert_eq!(store.get_answers(0).len(), 1);
    }
}

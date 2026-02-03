use crate::constraint::ConstraintOps;
use crate::queue::{AnswerReceiver, BlockedOn, RecvResult};
use crate::term::TermStore;
use parking_lot::Mutex;
use std::sync::Arc;

use super::{Work, WorkStep};

/// Join receiver work: consume joiner outputs from a queue.
#[derive(Clone, Debug)]
pub struct JoinReceiverWork<C: ConstraintOps> {
    receiver: Arc<Mutex<AnswerReceiver<C>>>,
    blocked: Option<BlockedOn>,
}

impl<C: ConstraintOps> JoinReceiverWork<C> {
    pub fn new(receiver: AnswerReceiver<C>) -> Self {
        Self {
            receiver: Arc::new(Mutex::new(receiver)),
            blocked: None,
        }
    }

    pub fn blocked_on(&self) -> Option<BlockedOn> {
        self.blocked.clone()
    }

    pub fn step(&mut self, _terms: &mut TermStore) -> WorkStep<C> {
        let receiver = self.receiver.lock();
        match receiver.try_recv() {
            RecvResult::Item(nf) => {
                self.blocked = None;
                WorkStep::Emit(nf, Box::new(Work::JoinReceiver(self.clone())))
            }
            RecvResult::Closed => WorkStep::Done,
            RecvResult::Empty => {
                self.blocked = Some(receiver.blocked_on());
                WorkStep::More(Box::new(Work::JoinReceiver(self.clone())))
            }
        }
    }
}

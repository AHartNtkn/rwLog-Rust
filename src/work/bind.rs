use crate::constraint::ConstraintOps;
use crate::factors::Factors;
use crate::nf::NF;
use crate::node::{step_node, Node, NodeStep};
use crate::term::TermStore;

use super::{CallMode, Env, PipeWork, Tables, Work, WorkStep};

/// Monadic bind for pipe splitting: feeds each source NF as the left
/// boundary of a fresh pipe instance.
///
/// When a pipe advances a front element (Call, And, Fix) and the remaining
/// pipe has mid elements, the remaining pipe's search depends on the
/// specific boundary that flows from the source. `BindWork` implements
/// this correctly: for each NF emitted by the source, it instantiates a
/// new pipe with that NF as left boundary, and returns `Split` to Or the
/// new pipe into the search tree.
///
/// This contrasts with `ComposeWork` (symmetric diagonal join), which runs
/// both sides independently. ComposeWork is correct when the right side's
/// NF stream doesn't depend on specific left input (e.g., when remaining
/// mid is empty and only boundary NFs remain). But when the remaining pipe
/// contains Calls or other search-producing elements, running it with a
/// generic boundary causes it to explore an unconstrained (potentially
/// infinite) search space.
#[derive(Clone, Debug)]
pub struct BindWork<C: ConstraintOps> {
    /// Source node that produces NF answers.
    source: Box<Node<C>>,
    /// Template for instantiating pipes per source NF.
    template: PipeTemplate<C>,
}

/// Captured state for instantiating a pipe per source NF.
#[derive(Clone, Debug)]
struct PipeTemplate<C: ConstraintOps> {
    mid: Factors<C>,
    right: Option<NF<C>>,
    env: Env<C>,
    tables: Tables<C>,
    call_mode: CallMode<C>,
}

impl<C: ConstraintOps> BindWork<C> {
    /// Create a new BindWork from a source node and remaining pipe state.
    pub fn new(
        source: Node<C>,
        mid: Factors<C>,
        right: Option<NF<C>>,
        env: Env<C>,
        tables: Tables<C>,
        call_mode: CallMode<C>,
    ) -> Self {
        Self {
            source: Box::new(source),
            template: PipeTemplate {
                mid,
                right,
                env,
                tables,
                call_mode,
            },
        }
    }

    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.source, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                let pipe_node = self.template.instantiate(*nf);
                let continuation = BindWork {
                    source: Box::new(rest),
                    template: self.template.clone(),
                };
                let continuation_node =
                    Node::Work(Box::new(Work::Bind(continuation)));
                WorkStep::Split(Box::new(pipe_node), Box::new(continuation_node))
            }
            NodeStep::Continue(rest) => {
                *self.source = rest;
                WorkStep::More(Box::new(Work::Bind(self.take())))
            }
            NodeStep::Exhausted => WorkStep::Done,
        }
    }

    #[cfg(test)]
    pub(crate) fn source(&self) -> &Node<C> {
        &self.source
    }

    fn take(&mut self) -> Self {
        Self {
            source: std::mem::replace(&mut self.source, Box::new(Node::Fail)),
            template: self.template.clone(),
        }
    }
}

impl<C: ConstraintOps> PipeTemplate<C> {
    /// Instantiate a pipe with the given NF as left boundary.
    fn instantiate(&self, nf: NF<C>) -> Node<C> {
        let mut pipe = PipeWork::with_env_and_tables(
            Some(nf),
            self.mid.clone(),
            self.right.clone(),
            self.env.clone(),
            self.tables.clone(),
        );
        pipe.call_mode = self.call_mode.clone();
        Node::Work(Box::new(Work::Pipe(Box::new(pipe))))
    }
}

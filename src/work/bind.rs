use crate::constraint::ConstraintOps;
use crate::factors::Factors;
use crate::nf::NF;
use crate::term::TermStore;

use super::pipe::PipeEnd;
use super::{CallMode, Env, PipeWork, Tables, Work, WorkSet, WorkSetStep, WorkStep};

/// Monadic bind for pipe splitting: feeds each source NF as a boundary
/// of a fresh pipe instance.
///
/// When a pipe advances a front or back element (Call, And, Fix) and the
/// remaining pipe has mid elements, the remaining pipe's search depends on
/// the specific boundary that flows from the source. `BindWork` implements
/// this correctly: for each NF emitted by the source, it instantiates a
/// new pipe with that NF as a boundary, and returns `Split` to Or the
/// new pipe into the search tree.
///
/// For front advancement, the source NF becomes the left boundary.
/// For back advancement, the source NF becomes the right boundary.
///
/// This contrasts with `ComposeWork` (symmetric diagonal join), which runs
/// both sides independently. ComposeWork is correct when the remaining
/// pipe's NF stream doesn't depend on specific input from the source
/// (e.g., when remaining mid is empty and only boundary NFs remain). But
/// when the remaining pipe contains search-producing elements and has no
/// far-side boundary to constrain them, running it with a generic boundary
/// causes it to explore an unconstrained (potentially infinite) search space.
#[derive(Clone, Debug)]
pub struct BindWork<C: ConstraintOps> {
    /// Source work set that produces NF answers.
    source: WorkSet<C>,
    /// Template for instantiating pipes per source NF.
    template: PipeTemplate<C>,
}

/// Captured state for instantiating a pipe per source NF.
#[derive(Clone, Debug)]
struct PipeTemplate<C: ConstraintOps> {
    left: Option<NF<C>>,
    mid: Factors<C>,
    right: Option<NF<C>>,
    env: Env<C>,
    tables: Tables<C>,
    call_mode: CallMode<C>,
    /// Which side the source NF binds to.
    bind_end: PipeEnd,
}

impl<C: ConstraintOps> BindWork<C> {
    /// Create a BindWork that binds source NFs as the left boundary
    /// (front advancement: source flows left-to-right into remaining pipe).
    pub(crate) fn new_front(
        source: WorkSet<C>,
        mid: Factors<C>,
        right: Option<NF<C>>,
        env: Env<C>,
        tables: Tables<C>,
        call_mode: CallMode<C>,
    ) -> Self {
        Self {
            source,
            template: PipeTemplate {
                left: None,
                mid,
                right,
                env,
                tables,
                call_mode,
                bind_end: PipeEnd::Front,
            },
        }
    }

    /// Create a BindWork that binds source NFs as the right boundary
    /// (back advancement: source flows right-to-left into remaining pipe).
    pub(crate) fn new_back(
        source: WorkSet<C>,
        left: Option<NF<C>>,
        mid: Factors<C>,
        env: Env<C>,
        tables: Tables<C>,
        call_mode: CallMode<C>,
    ) -> Self {
        Self {
            source,
            template: PipeTemplate {
                left,
                mid,
                right: None,
                env,
                tables,
                call_mode,
                bind_end: PipeEnd::Back,
            },
        }
    }

    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        match self.source.step(terms) {
            WorkSetStep::Emit(nf) => {
                let pipe_work = self.template.instantiate(nf);
                WorkStep::Split(Box::new(pipe_work), Box::new(Work::Bind(self.take())))
            }
            WorkSetStep::Continue => WorkStep::More(Box::new(Work::Bind(self.take()))),
            WorkSetStep::Exhausted => WorkStep::Done,
        }
    }

    #[cfg(test)]
    pub(crate) fn source(&self) -> &WorkSet<C> {
        &self.source
    }

    fn take(&mut self) -> Self {
        Self {
            source: std::mem::replace(&mut self.source, WorkSet::new()),
            template: self.template.clone(),
        }
    }
}

impl<C: ConstraintOps> PipeTemplate<C> {
    /// Instantiate a pipe with the given NF as a boundary.
    fn instantiate(&self, nf: NF<C>) -> Work<C> {
        let (left, right) = match self.bind_end {
            PipeEnd::Front => (Some(nf), self.right.clone()),
            PipeEnd::Back => (self.left.clone(), Some(nf)),
        };
        let mut pipe = PipeWork::with_env_and_tables(
            left,
            self.mid.clone(),
            right,
            self.env.clone(),
            self.tables.clone(),
        );
        pipe.call_mode = self.call_mode.clone();
        Work::Pipe(Box::new(pipe))
    }
}

pub mod compose;
pub mod dual;
pub mod meet;

pub use compose::compose_nf;
pub use dual::{dual_nf, dual_drop_fresh};
pub use meet::meet_nf;

pub mod compose;
pub mod dual;
pub mod meet;
mod util;

pub use compose::compose_nf;
pub use dual::{dual_drop_fresh, dual_nf};
pub use meet::meet_nf;

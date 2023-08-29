//! This module contains the common constants of the project
//!
//! # Example
//!
//! ```
//! use lp_toolbox::constants;
//! use lp_toolbox::equation::{DVar, Equation};
//! 
//! let eq = Equation::new(vec![DVar(2e0, 1)], constants::EqType::LTE, 4e0);
//! ```

#[derive(Debug, PartialEq)]
/// Possible equality type in a given equation
pub enum EqType {
    /// Equal (rhs == lhs)
    EQ = 1,

    /// Greater Than (rhs > lhs)
    GT = 2,

    /// Greater Than or Equal To (rhs >= lhs)
    GTE = 3,
    
    /// Less Than (rhs < lhs)
    LT = 4,

    /// Less Than or Equal To (rhs <= lhs)
    LTE = 5
}

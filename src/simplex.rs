//! This feature module contains the algorithm to solve a Maximization and Minimization problem
//! using the Simplex method.
//!
//! For given problem:
//! - Maximize: `12x + 16y = 0`
//! - Subjected To: 
//!     - `10x + 20y <= 120`
//!     - `8x + 8y <= 80`
//!     - `x >=0 & y >= 0`
//!
//! The Simplex Tableau will look something like this
//!
//! | Basic Variables | x | y | s1 | s2 | RHS | Ratio |
//! |---|---|---|---|---|---|---|
//! | s1 | 10 | 20 | 1 | 0 | 120 |   |
//! | s2 | 8 | 8 | 0 | 1 | 80 |   |
//! | z | -12 | -16 | 0 | 0 |   |   |

use crate::{
    coord::{Coord, NavDir},
    equation::Equation,
};

#[derive(Debug, PartialEq)]
/// Possible problem type
pub enum ProblemType {
    /// Maximization problem
    MAX = 1,

    /// Minimization problem
    MIN = 2,
}

#[derive(Debug)]
/// Represents the simplex table in a single iteration
pub struct SimplexTable {
    /// Iteration number while solving the simplex table
    iteration_no: u64,

    /// Problem type (maximization / minimization problem)
    problem_type: ProblemType,

    /// Z => Coeff.s of Objective fn (`aM`)
    z: Vec<f64>,

    /// Basic Variables => Variales of Objective fn (`xM`)
    basic_var: Vec<u64>,

    /// Entered Basic Variables => Variables who's values are at play
    entered_basic_var: Vec<u64>,

    /// RHS => The solution (values) to the Entered Basic Variables
    rhs: Vec<f64>,

    /// Ratio => The Column based on which the key row is calculated
    ratio: Vec<f64>,

    /// Simplex Tableau => Coeff.s of all conditional equations
    st_table: Vec<f64>,

    /// Key Column => The original value of the key column
    st_key_col: Vec<f64>,

    /// Key Row => The original value of the key row
    st_key_row: Vec<f64>,

    /// Key Element => The original value of the key element
    st_key_elem: f64,

    /// Simplex Tableau Width
    st_width: usize,

    /// Simplex Tableau Height
    st_height: usize,

    /// Resolved => The simplex resolution is reached
    is_resolved: bool,
}

impl SimplexTable {
    /// Creates a new Simplex Tableau
    ///
    /// # Arguments
    /// * `problem_type` - `ProblemType` describes wheather its MAX or MIN problem
    /// * `objective_fn` - `Equation` equation describing the objective function
    /// * `conditions` - `Vec<Equation>` a list of equations each describiting a condition the
    /// objection function is subjected to
    ///
    /// # Example
    ///
    /// ```
    /// use lp_toolbox::{
    ///     simplex::{ProblemType, SimplexTable},
    ///     constants::EqType,
    ///     equation::{DVar, Equation},
    /// };
    ///
    /// // Maximize `12x + 16y = Z`
    /// // Subjected to:
    /// // - `10x + 12y <= 120`
    /// // - `8x + 8y <= 80`
    /// // - `x & y >= 0`
    ///
    /// // 12x + 16y - 0s1 - 0s2 = Z
    /// let objective_fn = Equation::new(
    ///     vec![DVar(12e0, 1), DVar(16e0, 2), DVar(-0e0, 3), DVar(-0e0, 4)],
    ///     EqType::EQ,
    ///     0e0,
    /// );
    /// let subjected_to = vec![
    ///     // `10x + 20y + s1 + 0s2 <= 120`
    ///     Equation::new(
    ///         vec![DVar(10e0, 1), DVar(20e0, 2), DVar(1e0, 3), DVar(0e0, 4)],
    ///         EqType::LTE,
    ///         120e0,
    ///     ),
    ///     // `8x + 8y + 0s1 + s2 <= 80`
    ///     Equation::new(
    ///         vec![DVar(8e0, 1), DVar(8e0, 2), DVar(0e0, 3), DVar(1e0, 4)],
    ///         EqType::LTE,
    ///         80e0,
    ///     ),
    /// ];
    ///
    /// let simplex = SimplexTable::new(ProblemType::MAX, &objective_fn, &subjected_to);
    /// ```
    pub fn new(
        problem_type: ProblemType,
        objective_fn: &Equation,
        conditions: &Vec<Equation>,
    ) -> SimplexTable {
        let (z, basic_var) = SimplexTable::get_z_and_basic_vars(objective_fn);
        let entered_basic_var =
            SimplexTable::get_entered_basic_vars(&z, &basic_var, conditions.len());
        let rhs = SimplexTable::get_rhs(&conditions);
        let (st_table, st_height, st_width) = SimplexTable::get_soluton_table(&conditions);

        SimplexTable {
            iteration_no: 0,
            problem_type,
            z,
            basic_var,
            entered_basic_var,
            rhs,
            ratio: vec![0e0; conditions.len()],
            st_table,
            st_key_col: vec![0e0; st_height + 1], // The +1 is for the z row's value
            st_key_row: vec![0e0; st_width + 1],  // The +1 is for the rhs col's value
            st_key_elem: 0e0,
            st_height,
            st_width,
            is_resolved: false,
        }
    }

    /// Move table to the next iteration state. Returns `false` if resolved
    ///
    /// # Example
    ///
    /// ```
    /// use lp_toolbox::{
    ///     simplex::{ProblemType, SimplexTable},
    ///     constants::EqType,
    ///     equation::{DVar, Equation},
    /// };
    ///
    /// // Maximize `12x + 16y = Z`
    /// // Subjected to:
    /// // - `10x + 12y <= 120`
    /// // - `8x + 8y <= 80`
    /// // - `x & y >= 0`
    ///
    /// // 12x + 16y - 0s1 - 0s2 = Z
    /// let objective_fn = Equation::new(
    ///     vec![DVar(12e0, 1), DVar(16e0, 2), DVar(-0e0, 3), DVar(-0e0, 4)],
    ///     EqType::EQ,
    ///     0e0,
    /// );
    /// let subjected_to = vec![
    ///     // `10x + 20y + s1 + 0s2 <= 120`
    ///     Equation::new(
    ///         vec![DVar(10e0, 1), DVar(20e0, 2), DVar(1e0, 3), DVar(0e0, 4)],
    ///         EqType::LTE,
    ///         120e0,
    ///     ),
    ///     // `8x + 8y + 0s1 + s2 <= 80`
    ///     Equation::new(
    ///         vec![DVar(8e0, 1), DVar(8e0, 2), DVar(0e0, 3), DVar(1e0, 4)],
    ///         EqType::LTE,
    ///         80e0,
    ///     ),
    /// ];
    ///
    /// let mut simplex = SimplexTable::new(ProblemType::MAX, &objective_fn, &subjected_to);
    ///
    /// simplex.next(); // 1st Iter
    /// simplex.next(); // 2nd Iter (resolves it)
    ///
    /// assert!(!simplex.next()); // Early return's with false for resolved tableau
    /// ```
    pub fn next(&mut self) -> bool {
        if self.is_resolved {
            return false;
        }

        let key_col = self.update_key_col();
        let key_row = self.update_ratio();
        self.set_st_key_element(key_col, key_row);
        self.update_st_key_row(key_row);
        self.update_st_rest(key_row);
        self.update_entries(key_col, key_row);
        self.is_solved();
        self.iteration_no += 1;
        return !self.is_resolved;
    }

    fn st_coord(&self, x: usize, y: usize) -> Coord {
        return Coord::new(x, y, self.st_width, self.st_height);
    }

    fn is_solved(&mut self) {
        let optimality_fn = match self.problem_type {
            ProblemType::MAX => |&each: &f64| each >= 0e0,
            ProblemType::MIN => |&each: &f64| each <= 0e0,
        };
        self.is_resolved = self.z.iter().all(optimality_fn);
    }

    fn update_key_col(&mut self) -> usize {
        let mut smallest_value = f64::MAX;
        let mut key_col = 0;
        for i in 0..self.z.len() {
            if self.z[i] < smallest_value {
                smallest_value = self.z[i];
                key_col = i;
            }
        }
        for (i, key_coord) in self.st_coord(key_col, 0).iter(NavDir::DOWN).enumerate() {
            self.st_key_col[i] = self.st_table[key_coord.to_index()];
        }
        let last_idx = self.st_key_col.len() - 1;
        self.st_key_col[last_idx] = self.z[key_col];
        return key_col;
    }

    fn update_ratio(&mut self) -> usize {
        let mut smallest_val = f64::MAX;
        let mut key_row = 0;
        // Assumption is RHS and Ratio cols are skipping storing the Z row's values
        for i in 0..self.rhs.len() {
            let new_ratio = self.rhs[i] / self.st_key_col[i];
            if new_ratio < smallest_val {
                smallest_val = new_ratio;
                key_row = i;
            }
            self.ratio[i] = new_ratio;
        }
        for (i, key_coord) in self.st_coord(0, key_row).iter(NavDir::RIGHT).enumerate() {
            self.st_key_row[i] = self.st_table[key_coord.to_index()];
        }
        let last_idx = self.st_key_row.len() - 1;
        self.st_key_row[last_idx] = self.rhs[key_row];
        return key_row;
    }

    fn set_st_key_element(&mut self, key_col: usize, key_row: usize) {
        self.st_key_elem = self.st_table[self.st_coord(key_col, key_row).to_index()];
    }

    fn update_st_key_row(&mut self, key_row: usize) {
        let row_coord = self.st_coord(0, key_row);
        for rt_coord in row_coord.iter(NavDir::RIGHT) {
            self.st_table[rt_coord.to_index()] /= self.st_key_elem;
        }
        self.rhs[key_row] /= self.st_key_elem;
    }

    fn update_st_rest(&mut self, key_row: usize) {
        // Updating simplex tableau
        for dwn_coord in self.st_coord(0, 0).iter(NavDir::DOWN) {
            if dwn_coord.y == key_row {
                continue;
            }

            for rt_coord in dwn_coord.iter(NavDir::RIGHT) {
                let corres_key_col_val = self.st_key_col[rt_coord.y];
                let corres_key_row_val = self.st_key_row[rt_coord.x];
                self.st_table[rt_coord.to_index()] -=
                    (corres_key_col_val * corres_key_row_val) / self.st_key_elem;
            }
        }

        // Updating the RHS
        let last_row_idx = self.st_key_row.len() - 1;
        let corres_key_row_val = self.st_key_row[last_row_idx];
        for i in 0..self.rhs.len() {
            if i == key_row {
                continue;
            }
            let corres_key_col_val = self.st_key_col[i];
            self.rhs[i] -= (corres_key_col_val * corres_key_row_val) / self.st_key_elem;
        }

        // Updating Z
        let last_col_idx = self.st_key_col.len() - 1;
        let corres_key_col_val = self.st_key_col[last_col_idx];
        for i in 0..self.z.len() {
            let corres_key_row_value = self.st_key_row[i];
            self.z[i] -= (corres_key_row_value * corres_key_col_val) / self.st_key_elem;
        }
    }

    fn update_entries(&mut self, key_col: usize, key_row: usize) {
        self.entered_basic_var[key_row] = self.basic_var[key_col];
    }

    fn get_z_and_basic_vars(objective_fn: &Equation) -> (Vec<f64>, Vec<u64>) {
        let mut z = vec![];
        let mut basic_var = vec![];

        for d_var in objective_fn.iter() {
            z.push(-1e0 * d_var.0);
            basic_var.push(d_var.1)
        }

        return (z, basic_var);
    }

    fn get_entered_basic_vars(z: &Vec<f64>, basic_var: &Vec<u64>, no_of_slacks: usize) -> Vec<u64> {
        let mut entered_basic_var = vec![];

        let end_idx = z.len();
        let start_idx = end_idx - no_of_slacks;

        for i in start_idx..end_idx {
            entered_basic_var.push(basic_var[i]);
        }
        return entered_basic_var;
    }

    fn get_rhs(conditions: &Vec<Equation>) -> Vec<f64> {
        let mut solution = vec![];
        for cond in conditions.iter() {
            solution.push(cond.get_rhs());
        }
        return solution;
    }

    fn get_soluton_table(conditions: &Vec<Equation>) -> (Vec<f64>, usize, usize) {
        let mut st_table: Vec<f64> = vec![];
        let st_height = conditions.len();
        for cond in conditions.iter() {
            st_table.extend(cond.iter().map(|dv| dv.0));
        }
        let st_width = st_table.len() / st_height;
        return (st_table, st_height, st_width);
    }

}

#[cfg(test)]
mod simplex_tests {
    use super::{ProblemType, SimplexTable};
    use crate::{
        constants::EqType,
        equation::{DVar, Equation},
    };

    /// Setups the basic maximization problem
    ///
    /// Maximize `12x + 16y = Z`
    /// Subjected to:
    /// - `10x + 12y <= 120`
    /// - `8x + 8y <= 80`
    /// - `x & y >= 0`
    fn setup_max_problem() -> (ProblemType, Equation, Vec<Equation>) {
        // `12x + 16y + 0s1 + 0s2`
        let objective_fn = Equation::new(
            vec![DVar(12e0, 1), DVar(16e0, 2), DVar(-0e0, 3), DVar(-0e0, 4)],
            EqType::EQ,
            0e0,
        );

        let subjected_to = vec![
            // `10x + 20y + s1 + 0s2 <= 120`
            Equation::new(
                vec![DVar(10e0, 1), DVar(20e0, 2), DVar(1e0, 3), DVar(0e0, 4)],
                EqType::LTE,
                120e0,
            ),
            // `8x + 8y + 0s1 + s2 <= 80`
            Equation::new(
                vec![DVar(8e0, 1), DVar(8e0, 2), DVar(0e0, 3), DVar(1e0, 4)],
                EqType::LTE,
                80e0,
            ),
        ];

        return (ProblemType::MAX, objective_fn, subjected_to);
    }

    #[test]
    fn should_create_simplex_table() {
        let (problem_type, objective_fn, subjected_to) = setup_max_problem();
        let simplex = SimplexTable::new(problem_type, &objective_fn, &subjected_to);

        assert_eq!(simplex.iteration_no, 0);
        assert_eq!(simplex.problem_type, ProblemType::MAX);
        assert_eq!(simplex.z, vec![-12e0, -16e0, 0e0, 0e0]);
        assert_eq!(simplex.basic_var, vec![1, 2, 3, 4]);
        assert_eq!(simplex.entered_basic_var, vec![3, 4]);
        assert_eq!(simplex.rhs, vec![120e0, 80e0]);
        assert_eq!(simplex.ratio, vec![0e0, 0e0]);
        assert_eq!(
            simplex.st_table,
            vec![10e0, 20e0, 1e0, 0e0, 8e0, 8e0, 0e0, 1e0]
        );
        assert_eq!(simplex.st_height, 2);
        assert_eq!(simplex.st_width, 4);
    }

    #[test]
    fn should_solve_simplex_table() {
        let (problem_type, objective_fn, subjected_to) = setup_max_problem();
        let mut simplex = SimplexTable::new(problem_type, &objective_fn, &subjected_to);

        simplex.next();

        assert_eq!(simplex.entered_basic_var, vec![2, 4]);
        assert_eq!(simplex.rhs, vec![6e0, 32e0]);

        simplex.next();

        assert_eq!(simplex.entered_basic_var, vec![2, 1]);
        assert_eq!(simplex.rhs, vec![2e0, 8e0]);

        assert!(!simplex.next());
    }
}

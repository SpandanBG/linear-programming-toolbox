//! This module containts the untility to using matrix like coordinates in a
//! single array
//!
//! # Example
//!
//! ```
//! use lp_toolbox::coord::Coord;
//!
//! // coord (1, 1) in a 2x2 matrix
//! let coord = Coord::new(1, 1, 2, 2);
//!
//! assert_eq!(coord.x, 1);
//! assert_eq!(coord.y, 1);
//! ```

#[derive(Debug, Clone)]
/// Represents the coordinate in matrix of a fixed size
pub struct Coord {
    /// The x axis position
    pub x: usize,

    /// The y axis position
    pub y: usize,

    /// The height of the matrix
    height: usize,

    /// The width of the matrix
    width: usize,
}

#[derive(Debug)]
/// Possible coordinate navigation direction
pub enum NavDir {
    /// Move y = y - 1
    UP,

    /// Move y = y + 1
    DOWN,

    /// Move x = x - 1
    LEFT,

    /// Move x = x + 1
    RIGHT,
}

#[derive(Debug)]
/// Represents the iterator of a Coord to the direction given by NavDir
pub struct CoordIter(Option<Coord>, NavDir);

impl Coord {
    /// Creates a new coord with x and y directly
    ///
    /// # Arguments
    ///
    /// * `x` - `usize` the x axis location
    /// * `y` - `usize` the y axis location
    /// * `width` - `usize` the width of the matrix
    /// * `height` - `usize` the height of the matrix
    ///
    /// # Example
    ///
    /// ```
    /// use lp_toolbox::coord::Coord;
    ///
    /// // In a 2x2 matrix: coord (1, 1);
    /// let coord = Coord::new(1, 1, 2, 2);
    ///
    /// assert_eq!(coord.x, 1);
    /// assert_eq!(coord.y, 1);
    /// ```
    pub fn new(x: usize, y: usize, width: usize, height: usize) -> Coord {
        return Coord {
            x,
            y,
            width,
            height,
        };
    }

    /// Get the coordinate right the current one
    ///
    /// # Example
    ///
    /// ```
    /// use lp_toolbox::coord::Coord;
    ///
    /// // In a 2x2 matrix: coord (0, 1);
    /// let coord = Coord::new(0, 1, 2, 2);
    /// let idx = coord.to_index();
    ///
    /// assert_eq!(idx, 2);
    /// ```
    pub fn to_index(&self) -> usize {
        return self.y * self.width + self.x;
    }

    /// Create a coordinate iterator
    ///
    /// # Arguments
    /// * `dir` - `NavDir` The direction the coordinate to iterate towards
    ///
    /// # Example
    ///
    /// ```
    /// use lp_toolbox::coord::{Coord, NavDir};
    ///
    /// // A (1, 1) coordinate in a 2x2 matrix
    /// let coord = Coord::new(1, 1, 2, 2);
    ///
    /// let mut nav_up_iter = coord.iter(NavDir::UP);
    /// nav_up_iter.next();
    /// let next_up = nav_up_iter.next().unwrap();
    ///
    /// assert_eq!(next_up.x, 1);
    /// assert_eq!(next_up.y, 0);
    /// ```
    pub fn iter(&self, dir: NavDir) -> CoordIter {
        return CoordIter(Some(self.clone()), dir);
    }

    fn up(&self) -> Option<Self> {
        if self.y == 0 {
            return None;
        }

        return Some(Self {
            x: self.x,
            y: self.y - 1,
            width: self.width,
            height: self.height,
        });
    }

    fn down(&self) -> Option<Self> {
        if self.y == self.height - 1 {
            return None;
        }

        return Some(Self {
            x: self.x,
            y: self.y + 1,
            width: self.width,
            height: self.height,
        });
    }

    fn left(&self) -> Option<Self> {
        if self.x == 0 {
            return None;
        }

        return Some(Self {
            x: self.x - 1,
            y: self.y,
            width: self.width,
            height: self.height,
        });
    }

    fn right(&self) -> Option<Self> {
        if self.x == self.width - 1 {
            return None;
        }

        Some(Self {
            x: self.x + 1,
            y: self.y,
            width: self.width,
            height: self.height,
        })
    }
}

impl Iterator for CoordIter {
    type Item = Coord;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.is_none() {
            return None;
        }
        let curr = self.0.clone();
        self.0 = match &self.1 {
            NavDir::UP => self.0.as_ref().unwrap().up(),
            NavDir::DOWN => self.0.as_ref().unwrap().down(),
            NavDir::LEFT => self.0.as_ref().unwrap().left(),
            NavDir::RIGHT => self.0.as_ref().unwrap().right(),
        };
        return curr;
    }
}

#[cfg(test)]
mod coord_tests {
    use super::Coord;

    #[test]
    fn should_create_coords() {
        let coord = Coord::new(1, 1, 2, 2);

        assert_eq!(coord.x, 1);
        assert_eq!(coord.y, 1);
    }
}

#[cfg(test)]
mod coord_iter_tests {
    use super::{Coord, NavDir};

    fn setup_coord() -> Coord {
        // A 9x9 Matrix with coord at (4, 4);
        return Coord::new(4, 4, 9, 9);
    }

    #[test]
    fn should_iterate_to_top() {
        let coord = setup_coord();
        let mut no_of_asserts = 0;

        let up_iter = coord.iter(NavDir::UP);

        for (i, next_up_coord) in up_iter.enumerate() {
            assert_eq!(next_up_coord.x, 4);
            assert_eq!(next_up_coord.y, 4 - i);
            no_of_asserts += 1;
        }
        assert_eq!(no_of_asserts, 5);
    }

    #[test]
    fn should_iterate_to_bottom() {
        let coord = setup_coord();
        let mut no_of_asserts = 0;

        let up_iter = coord.iter(NavDir::DOWN);

        for (i, next_up_coord) in up_iter.enumerate() {
            assert_eq!(next_up_coord.x, 4);
            assert_eq!(next_up_coord.y, 4 + i);
            no_of_asserts += 1;
        }
        assert_eq!(no_of_asserts, 5);
    }

    #[test]
    fn should_iterate_to_left() {
        let coord = setup_coord();
        let mut no_of_asserts = 0;

        let up_iter = coord.iter(NavDir::LEFT);

        for (i, next_up_coord) in up_iter.enumerate() {
            assert_eq!(next_up_coord.x, 4 - i);
            assert_eq!(next_up_coord.y, 4);
            no_of_asserts += 1;
        }
        assert_eq!(no_of_asserts, 5);
    }

    #[test]
    fn should_iterate_to_right() {
        let coord = setup_coord();
        let mut no_of_asserts = 0;

        let up_iter = coord.iter(NavDir::RIGHT);

        for (i, next_up_coord) in up_iter.enumerate() {
            assert_eq!(next_up_coord.x, 4 + i);
            assert_eq!(next_up_coord.y, 4);
            no_of_asserts += 1;
        }
        assert_eq!(no_of_asserts, 5);
    }

    #[test]
    fn should_iterate_top_to_bottom_from_left_to_right() {
        // (0, 0) for a 10x10 matrix
        let coord = Coord::new(0, 0, 10, 10);

        let mut no_of_assertions = 0;

        for (i, rt_coord) in coord.iter(NavDir::RIGHT).enumerate() {
            for (j, dwn_coord) in rt_coord.iter(NavDir::DOWN).enumerate() {
                assert_eq!(dwn_coord.x, i);
                assert_eq!(dwn_coord.y, j);
                no_of_assertions += 1;
            }
        }

        assert_eq!(no_of_assertions, 100);
    }
}

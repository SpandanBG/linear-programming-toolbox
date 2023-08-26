//! This module containts the untility to using matrix like coordinates in a
//! single array
//!
//! # Example
//!
//! ```
//! use simplex_method_lp::coord::Coord;
//!
//! // In a 2x2 matrix, in a single 4 length array, the array index 3 will be
//! // coord (1, 1):
//! let coord = Coord::new(3, 2, 2);
//!
//! assert_eq!(coord.x, 1);
//! assert_eq!(coord.y, 1);
//! ```

#[derive(Debug)]
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

impl Coord {
    /// Creates a new coord out of an array index for fixed width and height
    ///
    /// # Arguments
    ///
    /// * `idx` - `usize` the array index
    /// * `width` - `usize` the width of the matrix
    /// * `height` - `usize` the height of the matrix
    ///
    /// # Example
    ///
    /// ```
    /// use simplex_method_lp::coord::Coord;
    ///
    /// // In a 2x2 matrix, in a single 4 length array, the array index 3 will be
    /// // coord (1, 1):
    /// let coord = Coord::new(3, 2, 2);
    /// ```
    pub fn new(idx: usize, width: usize, height: usize) -> Coord {
        let x = idx % width;
        let y = idx / width;
        return Coord {
            x,
            y,
            height,
            width,
        };
    }

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
    /// use simplex_method_lp::coord::Coord;
    ///
    /// // In a 2x2 matrix: coord (1, 1);
    /// let coord = Coord::new_raw(1, 1, 2, 2);
    ///
    /// assert_eq!(coord.x, 1);
    /// assert_eq!(coord.y, 1);
    /// ```
    pub fn new_raw(x: usize, y: usize, width: usize, height: usize) -> Coord {
        return Coord {
            x,
            y,
            width,
            height,
        };
    }

    /// Get the coordinate above the current one
    ///
    /// # Example
    ///
    /// ```
    /// use simplex_method_lp::coord::Coord;
    ///
    /// // In a 2x2 matrix: coord (1, 1);
    /// let coord = Coord::new_raw(1, 1, 2, 2);
    ///
    /// // up coordinate will be: coord (1, 0);
    /// let up = coord.up().unwrap();
    ///
    /// assert_eq!(up.x, 1);
    /// assert_eq!(up.y, 0);
    /// ```
    pub fn up(&self) -> Option<Self> {
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

    /// Get the coordinate below the current one
    ///
    /// # Example
    ///
    /// ```
    /// use simplex_method_lp::coord::Coord;
    ///
    /// // In a 2x2 matrix: coord (0, 0);
    /// let coord = Coord::new_raw(0, 0, 2, 2);
    ///
    /// // up coordinate will be: coord (0, 1);
    /// let down = coord.down().unwrap();
    ///
    /// assert_eq!(down.x, 0);
    /// assert_eq!(down.y, 1);
    /// ```
    pub fn down(&self) -> Option<Self> {
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
  
    /// Get the coordinate left the current one
    ///
    /// # Example
    ///
    /// ```
    /// use simplex_method_lp::coord::Coord;
    ///
    /// // In a 2x2 matrix: coord (1, 1);
    /// let coord = Coord::new_raw(1, 1, 2, 2);
    ///
    /// // up coordinate will be: coord (0, 1);
    /// let left = coord.left().unwrap();
    ///
    /// assert_eq!(left.x, 0);
    /// assert_eq!(left.y, 1);
    /// ```
    pub fn left(&self) -> Option<Self> {
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

    /// Get the coordinate right the current one
    ///
    /// # Example
    ///
    /// ```
    /// use simplex_method_lp::coord::Coord;
    ///
    /// // In a 2x2 matrix: coord (0, 0);
    /// let coord = Coord::new_raw(0, 0, 2, 2);
    ///
    /// // up coordinate will be: coord (1, 0);
    /// let right = coord.right().unwrap();
    ///
    /// assert_eq!(right.x, 1);
    /// assert_eq!(right.y, 0);
    /// ```
    pub fn right(&self) -> Option<Self> {
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

    /// Get the coordinate right the current one
    ///
    /// # Example
    ///
    /// ```
    /// use simplex_method_lp::coord::Coord;
    ///
    /// // In a 2x2 matrix: coord (0, 1);
    /// let coord = Coord::new_raw(0, 1, 2, 2);
    /// let idx = coord.to_index();
    ///
    /// assert_eq!(idx, 2);
    /// ```
    pub fn to_index(&self) -> usize {
        self.y * self.width + self.x
    }
}

#[cfg(test)]
mod coord_tests {
    use super::Coord;

    fn setup_coord(idx: usize) -> Coord {
        // in a 2x2 matrix represented by an array of size 4 
        // then, the index 2 is can be represented by (0, 1);
        return Coord::new(idx, 2, 2);
    }

    #[test]
    fn should_create_raw_coords() {
        let coord = Coord::new_raw(1, 1, 2, 2);

        assert_eq!(coord.x, 1);
        assert_eq!(coord.y, 1);
    }

    #[test]
    fn should_return_coords_for_index() {
        let coord = setup_coord(2);

        assert_eq!(coord.x, 0);
        assert_eq!(coord.y, 1);
    }

    #[test]
    fn should_return_none_for_up_coord() {
        let coord = setup_coord(0);

        let up = coord.up();

        assert!(up.is_none());
    }


    #[test]
    fn should_return_0_0_for_up_coord() {
        let coord = setup_coord(2);

        let up = coord.up();
        let up = up.unwrap();

        assert_eq!(up.x, 0);
        assert_eq!(up.y, 0);
    }

    #[test]
    fn should_return_none_for_left_coord() {
        let coord = setup_coord(0);

        let left = coord.left();

        assert!(left.is_none());
    }

    #[test]
    fn should_return_0_0_for_left_coord() {
        let coord = setup_coord(1);

        let left = coord.left();
        let left = left.unwrap();

        assert_eq!(left.x, 0);
        assert_eq!(left.y, 0);
    }

    #[test]
    fn should_return_none_for_right_coord() {
        let coord = setup_coord(1);

        let right = coord.right();

        assert!(right.is_none());
    }

    #[test]
    fn should_return_0_1_for_right_coord() {
        let coord = setup_coord(0);

        let right = coord.right();
        let right = right.unwrap();

        assert_eq!(right.x, 1);
        assert_eq!(right.y, 0);
    }


    #[test]
    fn should_return_none_for_down_coord() {
        let coord = setup_coord(2);

        let down = coord.down();

        assert!(down.is_none());
    }

    #[test]
    fn should_return_0_1_for_down_coord() {
        let coord = setup_coord(0);

        let down = coord.down();
        let down = down.unwrap();

        assert_eq!(down.x, 0);
        assert_eq!(down.y, 1);
    }

    #[test]
    fn should_return_index_from_coord() {
        let coord = setup_coord(2);

        let idx = coord.to_index();

        assert_eq!(idx, 2);
    }
}


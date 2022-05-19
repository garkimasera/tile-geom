use crate::Coords;
use serde::{Deserialize, Serialize};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Serialize, Deserialize)]
pub enum ShapeKind {
    OneTile,
    Line,
    Circle,
    // Sector,
    // All,
}

impl Default for ShapeKind {
    fn default() -> Self {
        ShapeKind::OneTile
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Serialize, Deserialize)]
pub enum Shape {
    OneTile { pos: Coords },
    Line { start: Coords, end: Coords },
    Circle { center: Coords, radius: u32 },
}

impl Shape {
    pub fn is_inside(&self, p: Coords) -> bool {
        match *self {
            Shape::OneTile { pos } => pos == p,
            Shape::Line { .. } => unimplemented!(),
            Shape::Circle { center, radius } => (center.mdistance(p) as u32) < radius,
        }
    }

    pub fn iter(&self) -> Vec<Coords> {
        match *self {
            Shape::OneTile { pos } => vec![pos],
            Shape::Line { .. } => unimplemented!(),
            Shape::Circle { center, radius } => {
                if radius == 0 {
                    return vec![center];
                }
                let radius = radius as i32;
                let r = radius as f32 + 0.5;
                let r2 = r * r;
                super::RectIter::new(
                    center - Coords::new(radius, radius),
                    center + Coords::new(radius, radius),
                )
                .filter(|pos| pos.distance2(center) < r2)
                .collect()
            }
        }
    }
}

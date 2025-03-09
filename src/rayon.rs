use rayon::prelude::IntoParallelIterator;

use super::Array2d;

impl<T: Send> IntoParallelIterator for Array2d<T> {
    type Item = T;
    type Iter = rayon::vec::IntoIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        self.v.into_par_iter()
    }
}

impl<'data, T: Sync + 'data> IntoParallelIterator for &'data Array2d<T> {
    type Item = &'data T;
    type Iter = rayon::slice::Iter<'data, T>;

    fn into_par_iter(self) -> Self::Iter {
        <&[T]>::into_par_iter(&self.v)
    }
}

impl<'data, T: Send + 'data> IntoParallelIterator for &'data mut Array2d<T> {
    type Item = &'data mut T;
    type Iter = rayon::slice::IterMut<'data, T>;

    fn into_par_iter(self) -> Self::Iter {
        <&mut [T]>::into_par_iter(&mut self.v)
    }
}

#[cfg(test)]
mod test {
    use crate::Coords;

    use super::*;
    use rayon::prelude::*;

    #[test]
    fn rayon_test() {
        let mut array_2d = Array2d::new(3, 3, 0);
        let size = array_2d.size();

        array_2d.par_iter_mut().enumerate().for_each(|(i, v)| {
            let p = Coords::from_index_size(i, size);
            *v = p.0 + p.1 * 3;
        });

        for (p, v) in array_2d.iter_with_idx() {
            assert_eq!(*v, p.0 + p.1 * 3);
        }

        let array_2d_add = Array2d::new(3, 3, 1);

        array_2d
            .par_iter_mut()
            .zip(array_2d_add.par_iter())
            .for_each(|(v, a)| {
                *v += a;
            });
        for (p, v) in array_2d.iter_with_idx() {
            assert_eq!(*v, p.0 + p.1 * 3 + 1);
        }
    }
}

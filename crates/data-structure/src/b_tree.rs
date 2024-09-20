use std::{
    cmp::Ordering,
    fmt::{Display, Write},
    mem,
};

use arrayvec::ArrayVec;

pub struct BTree<T, const M: usize>
where
    [(); M + 1]:,
{
    data: ArrayVec<T, M>,
    children: ArrayVec<Box<Node<T, M>>, { M + 1 }>,
}
enum Node<T, const M: usize>
where
    [(); M + 1]:,
{
    Internal(BTree<T, M>),
    Leaf(ArrayVec<T, M>),
}

impl<T, const M: usize> BTree<T, M>
where
    [(); M + 1]:,
{
    pub fn new() -> Self {
        BTree {
            data: ArrayVec::new(),
            children: ArrayVec::new(),
        }
    }
}

impl<T: Display, const M: usize> Display for BTree<T, M>
where
    [(); M + 1]:,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('[')?;

        if self.children.is_empty() {
            for (idx, data) in self.data.iter().enumerate() {
                data.fmt(f)?;

                if idx != self.data.len() - 1 {
                    f.write_str(",\n")?;
                }
            }
        } else {
            for (idx, data) in self.data.iter().enumerate() {
                self.children[idx].fmt(f)?;

                f.write_str(", ")?;
                data.fmt(f)?;
                f.write_char(',')?;
            }

            f.write_char(' ')?;

            self.children.last().unwrap().fmt(f)?;
        }

        f.write_char(']')?;

        Ok(())
    }
}

impl<T: Display, const M: usize> Display for Node<T, M>
where
    [(); M + 1]:,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Internal(intl) => intl.fmt(f)?,
            Node::Leaf(l) => {
                f.write_char('[')?;

                for (idx, data) in l.iter().enumerate() {
                    data.fmt(f)?;

                    if idx != l.len() - 1 {
                        f.write_str(", ")?;
                    }
                }

                f.write_char(']')?;
            }
        }

        Ok(())
    }
}

fn split<T, const M: usize>(
    mut arr: ArrayVec<T, M>,
    to_insert: usize,
    data: T,
) -> (ArrayVec<T, M>, T, ArrayVec<T, M>) {
    let mid = arr.len() / 2;
    match to_insert.cmp(&mid) {
        Ordering::Less => {
            let mid = mid - 1;
            let mut right = ArrayVec::new();
            right.extend(arr.drain(mid + 1..));

            let mid = arr.pop().unwrap();

            let mut left = arr;
            left.insert(to_insert, data);

            (left, mid, right)
        }
        Ordering::Equal => {
            let mut right = ArrayVec::new();
            right.extend(arr.drain(mid..));

            let left = arr;

            (left, data, right)
        }
        Ordering::Greater => {
            let mid = mid + 1;
            let mut right = ArrayVec::new();

            right.extend(arr.drain(mid..));
            right.insert(to_insert - mid, data);

            let mid = arr.pop().unwrap();

            let left = arr;

            (left, mid, right)
        }
    }
}

fn split_children<T, const M: usize>(
    mut arr: ArrayVec<T, M>,
    to_insert: usize,
    data: T,
) -> (ArrayVec<T, M>, ArrayVec<T, M>) {
    let mid = (arr.len() - 1) / 2;
    match to_insert.cmp(&mid) {
        Ordering::Less => {
            let mid = mid - 1;
            let mut right = ArrayVec::new();
            right.extend(arr.drain(mid..));

            let mut left = arr;
            left.insert(to_insert, data);

            (left, right)
        }
        Ordering::Equal => {
            let mut right = ArrayVec::new();
            right.extend(arr.drain(mid..));

            let mut left = arr;
            left.push(data);

            (left, right)
        }
        Ordering::Greater => {
            let mid = mid + 1;
            let mut right = ArrayVec::new();

            right.extend(arr.drain(mid..));
            right.insert(to_insert - mid, data);

            let left = arr;

            (left, right)
        }
    }
}

impl<T: Eq + Ord, const M: usize> BTree<T, M>
where
    [(); M + 1]:,
{
    pub fn search(&self, data: &T) -> Option<()> {
        match self.data.binary_search(data) {
            Ok(_) => Some(()),
            Err(i) => {
                if self.children.len() > 0 {
                    self.children[i].search(data)
                } else {
                    None
                }
            }
        }
    }

    fn split(&mut self, to_insert: usize, data: T, child: Option<Box<Node<T, M>>>) {
        let arr = self.data.take();
        let (left, new_data, right) = split(arr, to_insert, data);
        self.data.push(new_data);

        let (left, right) = if !self.children.is_empty() {
            let mut children = self.children.take();
            let (left_children, right_children) = if let Some(child) = child {
                split_children(children, to_insert + 1, child)
            } else {
                let mut right = ArrayVec::new();

                right.extend(children.drain(children.len() / 2 + 1..));

                (children, right)
            };

            let left = Node::Internal(BTree {
                data: left,
                children: left_children,
            });
            let right = Node::Internal(BTree {
                data: right,
                children: right_children,
            });

            (left, right)
        } else {
            let left = Node::Leaf(left);
            let right = Node::Leaf(right);

            (left, right)
        };

        self.children.push(Box::new(left));
        self.children.push(Box::new(right));
    }

    pub fn insert(&mut self, data: T) -> Option<T> {
        match self.data.binary_search(&data) {
            Ok(i) => Some(mem::replace(&mut self.data[i], data)),
            Err(i) => {
                if !self.children.is_empty() {
                    let (ret, up) = self.children[i].insert(data);
                    if let Some((data, child)) = up {
                        if self.data.is_full() {
                            self.split(i, data, Some(child))
                        } else {
                            self.data.insert(i, data);
                            self.children.insert(i + 1, child)
                        }
                    };

                    ret
                } else {
                    if self.data.is_full() {
                        self.split(i, data, None)
                    } else {
                        self.data.insert(i, data);
                    }

                    None
                }
            }
        }
    }

    pub fn delete(&mut self, data: &T) -> Option<T> {
        let data = match self.data.binary_search(data) {
            Ok(i) => {
                if self.children.is_empty() {
                    Some(self.data.remove(i))
                } else if self.children[i].len() > M / 2 {
                    let (data, action) = self.children[i].delete_tail();
                    let data = mem::replace(&mut self.data[i], data);

                    if action {
                        self.rotate(i);
                    }

                    Some(data)
                } else if self.children[i + 1].len() > M / 2 {
                    let (data, action) = self.children[i + 1].delete_head();
                    let data = mem::replace(&mut self.data[i], data);

                    if action {
                        self.rotate(i + 1);
                    }

                    Some(data)
                } else {
                    let data = self.data.remove(i);
                    let to_merge = self.children.remove(i + 1);
                    self.children[i].merge(*to_merge);

                    Some(data)
                }
            }
            Err(i) => {
                if self.children.is_empty() {
                    None
                } else {
                    let (data, action) = self.children[i].delete(data);

                    if action {
                        self.rotate(i);
                    }

                    data
                }
            }
        };

        if self.data.is_empty() && !self.children.is_empty() {
            let mut children = self.children.take();

            match *(children.remove(0)) {
                Node::Internal(intl) => *self = intl,
                Node::Leaf(l) => self.data = l,
            }
        }

        data
    }

    fn rotate(&mut self, i: usize) -> bool {
        if i > 0 && self.children[i - 1].len() > M / 2 {
            let (data, child) = match &mut *self.children[i - 1] {
                Node::Internal(intl) => (intl.data.pop().unwrap(), intl.children.pop()),
                Node::Leaf(l) => (l.pop().unwrap(), None),
            };
            let data = mem::replace(&mut self.data[i - 1], data);

            match (&mut *self.children[i], child) {
                (Node::Internal(_), None) | (Node::Leaf(_), Some(_)) => unreachable!(),
                (Node::Internal(intl), Some(child)) => {
                    intl.data.insert(0, data);
                    intl.children.insert(0, child)
                }
                (Node::Leaf(l), None) => l.insert(0, data),
            };

            false
        } else if i < self.children.len() - 1 && self.children[i + 1].len() > M / 2 {
            let (data, child) = match &mut *self.children[i + 1] {
                Node::Internal(intl) => (intl.data.remove(0), Some(intl.children.remove(0))),
                Node::Leaf(l) => (l.remove(0), None),
            };
            let data = mem::replace(&mut self.data[i], data);

            match (&mut *self.children[i], child) {
                (Node::Internal(_), None) | (Node::Leaf(_), Some(_)) => unreachable!(),
                (Node::Internal(intl), Some(child)) => {
                    intl.data.push(data);
                    intl.children.push(child)
                }
                (Node::Leaf(l), None) => l.push(data),
            };

            false
        } else {
            let data = self.data.remove(i - 1);

            if i > 0 {
                let child = self.children.remove(i);
                self.children[i - 1].merge_with_data(data, *child);
            } else {
                let child = self.children.remove(i + 1);
                self.children[i].merge_with_data(data, *child);
            }

            self.data.len() < M / 2
        }
    }
}

impl<T: Eq + Ord, const M: usize> Node<T, M>
where
    [(); M + 1]:,
{
    fn len(&self) -> usize {
        match self {
            Node::Internal(intl) => intl.data.len(),
            Node::Leaf(l) => l.len(),
        }
    }

    fn search(&self, data: &T) -> Option<()> {
        match self {
            Node::Internal(intl) => match intl.data.binary_search(data) {
                Ok(_) => Some(()),
                Err(i) => intl.children[i].search(data),
            },
            Node::Leaf(l) => match l.binary_search(data) {
                Ok(_) => Some(()),
                Err(_) => None,
            },
        }
    }

    fn insert(&mut self, data: T) -> (Option<T>, Option<(T, Box<Node<T, M>>)>) {
        match self {
            Node::Internal(intl) => match intl.data.binary_search(&data) {
                Ok(i) => (Some(mem::replace(&mut intl.data[i], data)), None),
                Err(i) => {
                    let (ret, up) = intl.children[i].insert(data);

                    let up = if let Some((data, child)) = up {
                        if intl.data.is_full() {
                            let arr = intl.data.take();
                            let (left, new_data, right) = split(arr, i, data);

                            let children = intl.children.take();
                            let (left_children, right_children) =
                                split_children(children, i + 1, child);

                            let right = Box::new(Node::Internal(BTree {
                                data: right,
                                children: right_children,
                            }));
                            let left = BTree {
                                data: left,
                                children: left_children,
                            };

                            *intl = left;

                            Some((new_data, right))
                        } else {
                            intl.data.insert(i, data);
                            intl.children.insert(i + 1, child);

                            None
                        }
                    } else {
                        None
                    };

                    (ret, up)
                }
            },
            Node::Leaf(l) => match l.binary_search(&data) {
                Ok(i) => (Some(mem::replace(&mut l[i], data)), None),
                Err(i) => {
                    let up = if l.is_full() {
                        let arr = l.take();
                        let (left, mid, right) = split(arr, i, data);

                        *l = left;

                        Some((mid, Box::new(Node::Leaf(right))))
                    } else {
                        l.insert(i, data);

                        None
                    };

                    (None, up)
                }
            },
        }
    }

    fn merge(&mut self, other: Self) {
        match (self, other) {
            (Node::Internal(l), Node::Internal(mut r)) => {
                l.data.extend(r.data);
                let last = l.children.len() - 1;
                l.children.extend(r.children.drain(1..));
                let first = r.children.remove(0);

                l.children[last].merge(*first);
            }
            (Node::Leaf(l), Node::Leaf(r)) => l.extend(r),
            (Node::Internal(_), Node::Leaf(_)) | (Node::Leaf(_), Node::Internal(_)) => {
                unreachable!()
            }
        }
    }

    fn merge_with_data(&mut self, data: T, other: Self) {
        match (self, other) {
            (Node::Internal(l), Node::Internal(r)) => {
                l.data.push(data);
                l.data.extend(r.data);
                l.children.extend(r.children);
            }
            (Node::Leaf(l), Node::Leaf(r)) => {
                l.push(data);
                l.extend(r)
            }
            (Node::Internal(_), Node::Leaf(_)) | (Node::Leaf(_), Node::Internal(_)) => {
                unreachable!()
            }
        }
    }

    fn delete_tail(&mut self) -> (T, bool) {
        match self {
            Node::Internal(intl) => intl.children.last_mut().unwrap().delete_tail(),
            Node::Leaf(l) => (l.pop().unwrap(), l.len() < M / 2),
        }
    }

    fn delete_head(&mut self) -> (T, bool) {
        match self {
            Node::Internal(intl) => intl.children[0].delete_head(),
            Node::Leaf(l) => (l.remove(0), l.len() < M / 2),
        }
    }

    fn delete(&mut self, data: &T) -> (Option<T>, bool) {
        match self {
            Node::Internal(intl) => match intl.data.binary_search(data) {
                Ok(i) => {
                    if intl.children[i].len() > M / 2 {
                        let (data, action) = intl.children[i].delete_tail();
                        let data = mem::replace(&mut intl.data[i], data);
                        let action = if action { intl.rotate(i) } else { false };

                        (Some(data), action)
                    } else if intl.children[i + 1].len() > M / 2 {
                        let (data, action) = intl.children[i + 1].delete_head();
                        let data = mem::replace(&mut intl.data[i], data);
                        let action = if action { intl.rotate(i + 1) } else { false };

                        (Some(data), action)
                    } else {
                        let data = intl.data.remove(i);
                        let to_merge = intl.children.remove(i + 1);
                        intl.children[i].merge(*to_merge);

                        (Some(data), intl.data.len() < M / 2)
                    }
                }
                Err(i) => {
                    let (data, action) = intl.children[i].delete(data);

                    let action = if action { intl.rotate(i) } else { false };

                    (data, action)
                }
            },
            Node::Leaf(l) => match l.binary_search(data) {
                Ok(i) => {
                    let data = l.remove(i);
                    (Some(data), l.len() < M / 2)
                }
                Err(_) => (None, false),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{BTree, Node};

    impl<T: Eq + Ord, const M: usize> Node<T, M>
    where
        [(); M + 1]:,
    {
        fn check(&self, min: Option<&T>, max: Option<&T>) {
            match self {
                Node::Internal(intl) => {
                    assert_eq!(intl.data.len() + 1, intl.children.len());
                    assert!(intl.data.len() >= M / 2);

                    for i in 0..intl.data.len() - 1 {
                        assert!(intl.data[i] < intl.data[i + 1]);

                        if intl.children.len() > i {
                            let min = if i == 0 {
                                None
                            } else {
                                Some(&intl.data[i - 1])
                            };
                            let max = Some(&intl.data[i]);

                            intl.children[i].check(min, max)
                        }
                    }

                    if let Some(last) = intl.children.last() {
                        last.check(intl.data.last(), None)
                    }

                    if let Some(min) = min {
                        assert!(min < &intl.data[0])
                    }

                    if let Some(max) = max {
                        assert!(max > intl.data.last().unwrap())
                    }
                }
                Node::Leaf(l) => {
                    assert!(l.len() >= M / 2);
                    for i in 0..l.len() - 1 {
                        assert!(l[i] < l[i + 1])
                    }

                    if let Some(min) = min {
                        assert!(min < &l[0])
                    }

                    if let Some(max) = max {
                        assert!(max > l.last().unwrap())
                    }
                }
            }
        }
    }

    impl<T: Eq + Ord, const M: usize> BTree<T, M>
    where
        [(); M + 1]:,
    {
        fn check(&self) {
            assert!(self.children.len() == 0 || self.children.len() == self.data.len() + 1);

            for i in 0..self.data.len() - 1 {
                assert!(self.data[i] < self.data[i + 1]);

                if !self.children.is_empty() {
                    let min = if i == 0 {
                        None
                    } else {
                        Some(&self.data[i - 1])
                    };
                    let max = Some(&self.data[i]);

                    self.children[i].check(min, max)
                }
            }

            if self.data.len() == 1 && !self.children.is_empty() {
                self.children[0].check(None, Some(&self.data[0]));
            }

            if let Some(last) = self.children.last() {
                last.check(self.data.last(), None)
            }
        }
    }

    #[test]
    fn basic() {
        let mut tree = BTree::<_, 5>::new();
        tree.insert(3);
        tree.insert(5);
        tree.insert(1);
        tree.insert(2);
        tree.insert(4);

        tree.check();

        assert_eq!(tree.search(&1), Some(()));
        assert_eq!(tree.search(&2), Some(()));
        assert_eq!(tree.search(&3), Some(()));
        assert_eq!(tree.search(&4), Some(()));
        assert_eq!(tree.search(&5), Some(()));
    }

    #[test]
    fn basic_split() {
        let mut tree = BTree::<_, 5>::new();
        tree.insert(3);
        tree.insert(6);
        tree.insert(4);
        tree.insert(1);
        tree.insert(2);
        tree.insert(5);

        tree.check();

        assert_eq!(tree.search(&5), Some(()));

        let mut tree = BTree::<_, 6>::new();
        tree.insert(3);
        tree.insert(6);
        tree.insert(7);
        tree.insert(4);
        tree.insert(5);
        tree.insert(2);
        tree.insert(1);

        tree.check();

        assert_eq!(tree.search(&1), Some(()));
    }

    #[test]
    fn leaf_split() {
        let mut tree = BTree::<_, 5>::new();
        tree.insert(3);
        tree.insert(6);
        tree.insert(4);
        tree.insert(5);
        tree.insert(2);
        tree.insert(1);
        tree.insert(7);
        tree.insert(8);
        tree.insert(9);

        tree.check();

        assert_eq!(tree.search(&9), Some(()));
    }

    #[test]
    fn many_split() {
        let mut tree = BTree::<_, 2>::new();

        for i in 0..32 {
            tree.insert(i);
            tree.check();
        }

        assert_eq!(tree.search(&9), Some(()));

        let mut tree = BTree::<_, 2>::new();

        for i in (0..32).rev() {
            tree.insert(i);
            tree.check();
        }

        assert_eq!(tree.search(&9), Some(()));
    }

    #[test]
    fn delete_root() {
        let mut tree = BTree::<_, 2>::new();

        for i in 0..15 {
            tree.insert(i);
            tree.check();
        }

        tree.delete(&7);
        tree.check();

        assert_eq!(tree.search(&7), None);
    }

    #[test]
    fn delete_complex() {
        let mut tree = BTree::<_, 5>::new();

        for i in 0..26 {
            tree.insert(i);
            tree.check();
        }

        tree.delete(&20);
        tree.check();

        tree.delete(&14);
        tree.check();

        tree.delete(&19);
        tree.check();

        tree.delete(&4);
        tree.check();
    }
}

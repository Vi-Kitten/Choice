//! Derivative Choice types from helper methods.
use super::*;

pub struct LeftFilterIter<I, A, B> {
    pub(super) iter: I,
    pub(super) _l: std::marker::PhantomData<A>,
    pub(super) _r: std::marker::PhantomData<B>
}

impl<I: Iterator<Item = Either<A, B>>, A, B> Iterator for LeftFilterIter<I, A, B> {
    type Item = A;

    fn next(&mut self) -> Option<A> {
        loop {
            match self.iter.next() {
                Some(Either::Left(a)) => break Some(a),
                Some(Either::Right(_)) => continue,
                None => break None,
            }
        }
    }
}

pub struct RightFilterIter<I, A, B> {
    pub(super) iter: I,
    pub(super) _l: std::marker::PhantomData<A>,
    pub(super) _r: std::marker::PhantomData<B>
}

impl<I: Iterator<Item = Either<A, B>>, A, B> Iterator for RightFilterIter<I, A, B> {
    type Item = B;

    fn next(&mut self) -> Option<B> {
        loop {
            match self.iter.next() {
                Some(Either::Left(_)) => continue,
                Some(Either::Right(b)) => break Some(b),
                None => break None,
            }
        }
    }
}

pub struct Swap<T> {
    pub(super) choice: T
}

impl<T: Choice<A, B>, A, B> DynChoice<B, A> for Swap<T> {
    fn into_left(self: Box<Self>) -> B {
        self.choice.right()
    }

    fn into_right(self: Box<Self>) -> A {
        self.choice.left()
    }
}

pub struct ChooseMap<T, U, A, B, F, G> {
    pub(super) choice: T,
    pub(super) other: U,
    pub(super) _l: std::marker::PhantomData<A>,
    pub(super) _r: std::marker::PhantomData<B>,
    pub(super) _f: std::marker::PhantomData<F>,
    pub(super) _g: std::marker::PhantomData<G>
}

impl<T: Choice<A, B>, U: Choice<F, G>, A, B, C, D, F: FnOnce(A) -> C, G: FnOnce(B) -> D> DynChoice<C, D> for ChooseMap<T, U, A, B, F, G> {
    fn into_left(self: Box<Self>) -> C {
        (self.other.left())(self.choice.left())
    }

    fn into_right(self: Box<Self>) -> D {
        (self.other.right())(self.choice.right())
    }
}

pub struct LeftCoBind<T, A, F> {
    pub(super) choice: T,
    pub(super) cobind: F,
    pub(super) _l: std::marker::PhantomData<A>
}

impl<T: Choice<A, B>, A, B, C, F: FnOnce(T) -> C> DynChoice<C, B> for LeftCoBind<T, A, F> {
    fn into_left(self: Box<Self>) -> C {
        (self.cobind)(self.choice)
    }

    fn into_right(self: Box<Self>) -> B {
        self.choice.right()
    }
}

pub struct RightCoBind<T, B, F> {
    pub(super) choice: T,
    pub(super) cobind: F,
    pub(super) _r: std::marker::PhantomData<B>
}

impl<T: Choice<A, B>, A, B, C, F: FnOnce(T) -> C> DynChoice<A, C> for RightCoBind<T, B, F> {
    fn into_left(self: Box<Self>) -> A {
        self.choice.left()
    }

    fn into_right(self: Box<Self>) -> C {
        (self.cobind)(self.choice)
    }
}
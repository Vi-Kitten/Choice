//! Derivative Choice types from helper methods.
use super::*;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct LeftFilterIter<I, A, B> {
    pub(super) iter: I,
    pub(super) _l: std::marker::PhantomData<A>,
    pub(super) _r: std::marker::PhantomData<B>,
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

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct RightFilterIter<I, A, B> {
    pub(super) iter: I,
    pub(super) _l: std::marker::PhantomData<A>,
    pub(super) _r: std::marker::PhantomData<B>,
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

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Swap<T> {
    pub(super) choice: T,
}

impl<T: Choice> DynChoice for Swap<T> {
    type Left = T::Right;
    type Right = T::Left;

    fn into_left(self: Box<Self>) -> T::Right {
        self.choice.right()
    }

    fn into_right(self: Box<Self>) -> T::Left {
        self.choice.left()
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct ChooseMap<T, U> {
    pub(super) choice: T,
    pub(super) other: U,
}

impl<T: Choice, U: Choice, C, D> DynChoice for ChooseMap<T, U>
where
    U::Left: FnOnce(T::Left) -> C,
    U::Right: FnOnce(T::Right) -> D,
{
    type Left = C;
    type Right = D;

    fn into_left(self: Box<Self>) -> C {
        (self.other.left())(self.choice.left())
    }

    fn into_right(self: Box<Self>) -> D {
        (self.other.right())(self.choice.right())
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct LeftCoBind<T, F> {
    pub(super) choice: T,
    pub(super) cobind: F,
}

impl<T: Choice, C, F: FnOnce(T) -> C> DynChoice for LeftCoBind<T, F> {
    type Left = C;
    type Right = T::Right;

    fn into_left(self: Box<Self>) -> C {
        (self.cobind)(self.choice)
    }

    fn into_right(self: Box<Self>) -> T::Right {
        self.choice.right()
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct RightCoBind<T, F> {
    pub(super) choice: T,
    pub(super) cobind: F,
}

impl<T: Choice, C, F: FnOnce(T) -> C> DynChoice for RightCoBind<T, F> {
    type Left = T::Left;
    type Right = C;

    fn into_left(self: Box<Self>) -> T::Left {
        self.choice.left()
    }

    fn into_right(self: Box<Self>) -> C {
        (self.cobind)(self.choice)
    }
}

use impl_trait_for_tuples::*;

#[impl_for_tuples(0, 16)]
impl DynChoice for Tuple {
    for_tuples!( type Left = ( #( Tuple::Left ),* ); );
    for_tuples!( type Right = ( #( Tuple::Right ),* ); );

    fn into_left(self: Box<Self>) -> Self::Left {
        for_tuples!( ( #( self.Tuple.left() ),* ) )
    }

    fn into_right(self: Box<Self>) -> Self::Right {
        for_tuples!( ( #( self.Tuple.right() ),* ) )
    }
}

pub mod derivatives;
use derivatives::*;

/// Dynamism bootstrapper for Choice
pub trait DynChoice {
    type Left;
    type Right;
    /// Convert into `A`
    fn into_left(self: Box<Self>) -> Self::Left;

    /// Convert into `B`
    fn into_right(self: Box<Self>) -> Self::Right;
}

/// Represents the affine negation of `Either`.
///
/// It represents a conjunctive union.
pub trait Choice: DynChoice + Sized {
    /// Convert into `A`
    fn left(self: Self) -> Self::Left;
    /// Convert into `B`
    fn right(self: Self) -> Self::Right;

    /// Maps the left value.
    ///
    /// This treats Choice as a functor in the left type.
    fn map_left<C, F: FnOnce(Self::Left) -> C>(
        self,
        left: F,
    ) -> ChooseMap<Self, Both<F, fn(Self::Right) -> Self::Right>> {
        self.map_both(left, std::convert::identity)
    }

    /// Maps the right value.
    ///
    /// This treats Choice as a functor in the right type.
    fn map_right<C, G: FnOnce(Self::Right) -> C>(
        self,
        right: G,
    ) -> ChooseMap<Self, Both<fn(Self::Left) -> Self::Left, G>> {
        self.map_both(std::convert::identity, right)
    }

    /// Maps both values.
    ///
    /// This treats Choice as a functor in both the left and right types.
    fn map_both<C, D, F: FnOnce(Self::Left) -> C, G: FnOnce(Self::Right) -> D>(
        self,
        left: F,
        right: G,
    ) -> ChooseMap<Self, Both<F, G>> {
        self.choose_map(Both::new(left, right))
    }

    /// Composes a choice of values with a choice of functions to produce a choice of values.
    ///
    /// This sequences the choices in a way that is unique to the structure of a choice.
    fn choose_map<T: Choice, C, D>(self, choice: T) -> ChooseMap<Self, T>
    where
        T::Left: FnOnce(Self::Left) -> C,
        T::Right: FnOnce(Self::Right) -> D,
    {
        ChooseMap {
            choice: self,
            other: choice,
        }
    }

    /// Sets the left value to a map from the current state to be ran if chosen.
    ///
    /// This treats Choice as a co-monad in the left type.
    fn cobind_left<C, F: FnOnce(Self) -> C>(self, left: F) -> LeftCoBind<Self, F> {
        LeftCoBind {
            choice: self,
            cobind: left,
        }
    }

    /// Sets the right value to a map from the current state to be ran if chosen.
    ///
    /// This treats Choice as a co-monad in the right type.
    fn cobind_right<C, G: FnOnce(Self) -> C>(self, right: G) -> RightCoBind<Self, G> {
        RightCoBind {
            choice: self,
            cobind: right,
        }
    }

    /// Swaps the left and right values.
    fn swap(self) -> Swap<Self> {
        Swap { choice: self }
    }

    /// Composes a choice of values with an either of functions to produce a single value.
    ///
    /// The composition of a choice with its linear negative annihilates both.
    fn choose<C, F: FnOnce(Self::Left) -> C, G: FnOnce(Self::Right) -> C>(
        self,
        either: Either<F, G>,
    ) -> C {
        match either {
            Either::Left(f) => (f)(self.left()),
            Either::Right(g) => (g)(self.right()),
        }
    }
}

impl<A, B> DynChoice for Box<dyn DynChoice<Left = A, Right = B>> {
    type Left = A;
    type Right = B;

    fn into_left(self: Box<Self>) -> A {
        (*self).into_left()
    }

    fn into_right(self: Box<Self>) -> B {
        (*self).into_right()
    }
}

/// A choice between filterning eithers by branch.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct IterChoice<I> {
    iter: I,
}

impl<I> IterChoice<I> {
    pub fn new(iter: I) -> IterChoice<I> {
        IterChoice { iter }
    }
}

impl<I: Iterator<Item = Either<A, B>>, A, B> DynChoice for IterChoice<I> {
    type Left = LeftFilterIter<I, A, B>;
    type Right = RightFilterIter<I, A, B>;

    /// Creates an iterator that filters for left.
    fn into_left(self: Box<Self>) -> LeftFilterIter<I, A, B> {
        LeftFilterIter {
            iter: self.iter,
            _l: std::marker::PhantomData,
            _r: std::marker::PhantomData,
        }
    }

    /// Creates an iterator that filters for right.
    fn into_right(self: Box<Self>) -> RightFilterIter<I, A, B> {
        RightFilterIter {
            iter: self.iter,
            _l: std::marker::PhantomData,
            _r: std::marker::PhantomData,
        }
    }
}

impl<A, B> DynChoice for Vec<Either<A, B>> {
    type Left = Vec<A>;
    type Right = Vec<B>;

    fn into_left(self: Box<Self>) -> Vec<A> {
        IterChoice::new((*self).into_iter()).left().collect()
    }

    fn into_right(self: Box<Self>) -> Vec<B> {
        IterChoice::new((*self).into_iter()).right().collect()
    }
}

impl<A, B> DynChoice for Box<[Either<A, B>]> {
    type Left = Box<[A]>;
    type Right = Box<[B]>;

    fn into_left(self: Box<Self>) -> Box<[A]> {
        (*self).into_vec().left().into_boxed_slice()
    }

    fn into_right(self: Box<Self>) -> Box<[B]> {
        (*self).into_vec().right().into_boxed_slice()
    }
}

impl<T> Choice for T
where
    T: DynChoice + Sized,
{
    fn left(self: Self) -> T::Left {
        Box::new(self).into_left()
    }

    fn right(self: Self) -> T::Right {
        Box::new(self).into_right()
    }
}

/// Stores a DynChoice with indirection so that Choice can be implemented
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct BoxedChoice<C: ?Sized> {
    choice: Box<C>,
}

impl<C: ?Sized> BoxedChoice<C> {
    pub fn new(choice: Box<C>) -> BoxedChoice<C> {
        BoxedChoice { choice }
    }
}

impl<C: ?Sized + DynChoice> DynChoice for BoxedChoice<C> {
    type Left = C::Left;
    type Right = C::Right;

    fn into_left(self: Box<Self>) -> C::Left {
        self.choice.into_left()
    }

    fn into_right(self: Box<Self>) -> C::Right {
        self.choice.into_right()
    }
}

/// A choice with both branches identical.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Same<A> {
    val: A,
}

impl<A> Same<A> {
    /// Constructs a choice with both branches identical.
    pub fn new(val: A) -> Same<A> {
        Same { val }
    }
}

impl<A> DynChoice for Same<A> {
    type Left = A;
    type Right = A;

    fn into_left(self: Box<Self>) -> A {
        self.val
    }

    fn into_right(self: Box<Self>) -> A {
        self.val
    }
}

/// A choice with both branches already inhabited.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Both<A, B> {
    left: A,
    right: B,
}

impl<A, B> Both<A, B> {
    /// Constructs a choice with both branches already inhabited.
    pub fn new(left: A, right: B) -> Both<A, B> {
        Both { left, right }
    }
}

impl<A, B> DynChoice for Both<A, B> {
    type Left = A;
    type Right = B;

    fn into_left(self: Box<Self>) -> A {
        self.left
    }

    fn into_right(self: Box<Self>) -> B {
        self.right
    }
}

/// A choice using with lazy expressions.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Lazy<A, B, F: FnOnce() -> A, G: FnOnce() -> B> {
    left: F,
    right: G,
}

impl<A, B, F: FnOnce() -> A, G: FnOnce() -> B> Lazy<A, B, F, G> {
    /// Constructs a choice using lazy expressions.
    pub fn new(left: F, right: G) -> Lazy<A, B, F, G> {
        Lazy { left, right }
    }
}

impl<A, B, F: FnOnce() -> A, G: FnOnce() -> B> DynChoice for Lazy<A, B, F, G> {
    type Left = A;
    type Right = B;

    fn into_left(self: Box<Self>) -> A {
        (self.left)()
    }

    fn into_right(self: Box<Self>) -> B {
        (self.right)()
    }
}

/// A choice with a common resource.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Exclusive<T, F, G> {
    common: T,
    left: F,
    right: G,
}

impl<T, A, B, F: FnOnce(T) -> A, G: FnOnce(T) -> B> Exclusive<T, F, G> {
    /// Constructs a choice with a common resource.
    pub fn new(common: T, left: F, right: G) -> Exclusive<T, F, G> {
        Exclusive {
            common,
            left,
            right,
        }
    }
}

impl<T, A, B, F: FnOnce(T) -> A, G: FnOnce(T) -> B> DynChoice for Exclusive<T, F, G> {
    type Left = A;
    type Right = B;

    fn into_left(self: Box<Self>) -> A {
        (self.left)(self.common)
    }

    fn into_right(self: Box<Self>) -> B {
        (self.right)(self.common)
    }
}

/// An Exclusive choice implemented using function pointers.
pub type ExclusiveFn<T, A, B> = Exclusive<T, fn(T) -> A, fn(T) -> B>;

/// A type with two possile states, `Left` or `Right`.
///
/// It represents a disjunctive union.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A, B> Either<A, B> {
    /// Chooses the branch of the either dependent on the boolean provided.
    ///
    /// - `true` creates `Left`.
    /// - `false` creates `Right`.
    pub fn branch(choice: bool) -> Either<A, B>
    where
        A: Default,
        B: Default,
    {
        if choice {
            Either::Left(Default::default())
        } else {
            Either::Right(Default::default())
        }
    }

    /// Sets the left branch from a result assuming `Ok`, otherwise if `Err` sets the right branch instead.
    pub fn ok_into_left(result: Result<A, B>) -> Either<A, B> {
        result.map_or_else(Either::Right, Either::Left)
    }

    /// Sets the right branch from a result assuming `Ok`, otherwise if `Err` sets the left branch instead.
    pub fn ok_into_right(result: Result<B, A>) -> Either<A, B> {
        result.map_or_else(Either::Left, Either::Right)
    }

    /// Moves out of the either, if left then the result is `Ok`, otherwise the result is an `Err`.
    pub fn left(self) -> Result<A, B> {
        self.either(Result::Ok, Result::Err)
    }

    /// Moves out of the either, if right then the result is `Ok`, otherwise the result is an `Err`.
    pub fn right(self) -> Result<B, A> {
        self.either(Result::Err, Result::Ok)
    }

    /// Converts from `&Either<A, B>` to `Either<&A, &B>`
    pub fn as_ref(&self) -> Either<&A, &B> {
        match self {
            Either::Left(a) => Either::Left(a),
            Either::Right(b) => Either::Right(b),
        }
    }

    /// Converts from `&mut Either<A, B>` to `Either<&mut A, &mut B>`
    pub fn as_mut(&mut self) -> Either<&mut A, &mut B> {
        match self {
            Either::Left(a) => Either::Left(a),
            Either::Right(b) => Either::Right(b),
        }
    }

    /// Maps the left value.
    ///
    /// This treats Either as a functor in the left type.
    pub fn map_left<C>(self, left: impl FnOnce(A) -> C) -> Either<C, B> {
        self.map_either(left, std::convert::identity)
    }

    /// Maps the left value.
    ///
    /// This treats Either as a functor in the right type.
    pub fn map_right<C>(self, right: impl FnOnce(B) -> C) -> Either<A, C> {
        self.map_either(std::convert::identity, right)
    }

    /// Maps both values.
    ///
    /// This treats Either as a functor in both the left and right types.
    pub fn map_either<C, D>(
        self,
        left: impl FnOnce(A) -> C,
        right: impl FnOnce(B) -> D,
    ) -> Either<C, D> {
        self.choose_map(Both::new(left, right))
    }

    /// Composes an either with a choice of functions to produce an either of values.
    ///
    /// This sequences the either and choice in a way that is unique to their structures.
    pub fn choose_map<C, D, F: FnOnce(A) -> C, G: FnOnce(B) -> D>(
        self,
        choice: impl Choice<Left = F, Right = G>,
    ) -> Either<C, D> {
        match self {
            Either::Left(a) => Either::Left((choice.left())(a)),
            Either::Right(b) => Either::Right((choice.right())(b)),
        }
    }

    /// Composes an either with a choice of values to produce an either of values.
    ///
    /// This sequences the either and choice in a way that is unique to their structures.
    pub fn compose<C, D>(self, choice: impl Choice<Left = C, Right = D>) -> Either<(A, C), (B, D)> {
        self.choose_map(choice.map_both(|c| move |a| (a, c), |d| move |b| (b, d)))
    }

    /// Maps the left if present to create a new either.
    ///
    /// This treats Either as a monad in the left type.
    pub fn bind_left<C>(self, left: impl FnOnce(A) -> Either<C, B>) -> Either<C, B> {
        self.either(left, Either::Right)
    }

    /// Maps the right if present to create a new either.
    ///
    /// This treats Either as a monad in the right type.
    pub fn bind_right<C>(self, right: impl FnOnce(B) -> Either<A, C>) -> Either<A, C> {
        self.either(Either::Left, right)
    }

    /// Swaps the left and right values.
    pub fn swap(self) -> Either<B, A> {
        self.either(Either::Right, Either::Left)
    }

    /// Handles each case of the either to produce a single value.
    pub fn either<C>(self, left: impl FnOnce(A) -> C, right: impl FnOnce(B) -> C) -> C {
        self.choose_either(Both::new(left, right))
    }

    /// Composes an either with a choice of functions to produce a single value.
    ///
    /// The composition of an either with its linear negative annihilates both.
    pub fn choose_either<C, F: FnOnce(A) -> C, G: FnOnce(B) -> C>(
        self,
        choice: impl Choice<Left = F, Right = G>,
    ) -> C {
        match self {
            Either::Left(a) => (choice.left())(a),
            Either::Right(b) => (choice.right())(b),
        }
    }

    /// Converts a consumer of an either into a choice of consumers.
    pub fn factor<C, F: FnOnce(Either<A, B>) -> C>(
        consumer: F,
    ) -> ExclusiveFn<F, impl FnOnce(A) -> C, impl FnOnce(B) -> C> {
        Exclusive::new(
            consumer,
            |consumer| move |a| (consumer)(Either::Left(a)),
            |consumer| move |b| (consumer)(Either::Right(b)),
        )
    }

    /// Converts a choice of consumers into a consumer of an either.
    pub fn distribute<C, F: FnOnce(A) -> C, G: FnOnce(B) -> C>(
        choice: impl Choice<Left = F, Right = G>,
    ) -> impl FnOnce(Either<A, B>) -> C {
        move |either| match either {
            Either::Left(a) => choice.left()(a),
            Either::Right(b) => choice.right()(b),
        }
    }
}

impl<A> Either<A, A> {
    /// Consume an either with branches of same type to produce a single value.
    pub fn converge(self) -> A {
        self.either(std::convert::identity, std::convert::identity)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_swap() {
        let a = Both::new(0, 1);
        let b = Both::new(2, 3);
        let ab = (a, b.swap());
        assert_eq!(ab.left(), (0, 3))
    }

    #[test]
    fn test_either_map() {
        let mut a = Either::Left(0);
        a = a.map_right(|x: i32| x + 1);
        assert_eq!(a.as_ref(), Either::Left(&0));
        a = a.map_left(|x: i32| x + 1);
        assert_eq!(a.as_ref(), Either::Left(&1));
        a = a.map_either(|x| x * 2, |x| x * 3);
        assert_eq!(a, Either::Left(2));

        let mut b = Either::Right(0);
        b = b.map_left(|x: i32| x + 1);
        assert_eq!(b.as_ref(), Either::Right(&0));
        b = b.map_right(|x: i32| x + 1);
        assert_eq!(b.as_ref(), Either::Right(&1));
        b = b.map_either(|x| x * 2, |x| x * 3);
        assert_eq!(b, Either::Right(3))
    }

    #[test]
    fn test_choice_map() {
        let a = Both::new(1, -1).map_right(|x: i32| x - 1);
        assert_eq!(a.left(), 1);
        assert_eq!(a.right(), -2);
        let a = a.map_left(|x: i32| x + 1);
        assert_eq!(a.left(), 2);
        assert_eq!(a.right(), -2);
        let a = a.map_both(|x| x * 2, |x| x * 3);
        assert_eq!(a.left(), 4);
        assert_eq!(a.right(), -6)
    }

    #[test]
    fn test_composition() {
        let a = Both::new(0, 1).choose_map(Both::new(|x| x + 1, |x| x - 1));
        assert_eq!(a.left(), 1);
        assert_eq!(a.right(), 0);
        assert_eq!(
            Both::new(0, 1).choose(Either::<fn(i32) -> i32, fn(i32) -> i32>::Left(
                |x: i32| x + 1
            )),
            1
        );
        assert_eq!(
            Both::new(0, 1).choose(Either::<fn(i32) -> i32, fn(i32) -> i32>::Right(
                |x: i32| x - 1
            )),
            0
        )
    }

    #[test]
    fn test_bind() {
        fn test_left(a: Either<i32, i32>, b: Either<i32, i32>) -> Either<i32, i32> {
            a.bind_left(|x| b.map_left(move |y| x + y))
        }
        assert_eq!(test_left(Either::Left(1), Either::Left(2)), Either::Left(3));
        assert_eq!(
            test_left(Either::Left(1), Either::Right(-2)),
            Either::Right(-2)
        );
        assert_eq!(
            test_left(Either::Right(-1), Either::Left(2)),
            Either::Right(-1)
        );
        assert_eq!(
            test_left(Either::Right(-1), Either::Right(-2)),
            Either::Right(-1)
        );
        fn test_right(a: Either<i32, i32>, b: Either<i32, i32>) -> Either<i32, i32> {
            a.bind_right(|x| b.map_right(move |y| x + y))
        }
        assert_eq!(
            test_right(Either::Right(-1), Either::Right(-2)),
            Either::Right(-3)
        );
        assert_eq!(
            test_right(Either::Right(-1), Either::Left(2)),
            Either::Left(2)
        );
        assert_eq!(
            test_right(Either::Left(1), Either::Right(-2)),
            Either::Left(1)
        );
        assert_eq!(
            test_right(Either::Left(1), Either::Left(2)),
            Either::Left(1)
        )
    }

    #[test]
    fn test_cobind() {
        let a = Both::new(1, -1);
        assert_eq!(a.cobind_left(|x| x.left()).left(), 1);
        assert_eq!(a.cobind_left(|x| x.left()).right(), -1);
        assert_eq!(a.cobind_left(|x| x.right()).left(), -1);
        assert_eq!(a.cobind_left(|x| x.right()).right(), -1);
        assert_eq!(a.cobind_right(|x| x.left()).left(), 1);
        assert_eq!(a.cobind_right(|x| x.left()).right(), 1);
        assert_eq!(a.cobind_right(|x| x.right()).left(), 1);
        assert_eq!(a.cobind_right(|x| x.right()).right(), -1)
    }

    #[test]
    fn test_filtering() {
        let a: Vec<Either<i32, i32>> = vec![
            Either::Left(0),
            Either::Right(1),
            Either::Left(2),
            Either::Right(3),
            Either::Left(4),
        ];
        assert_eq!(
            IterChoice::new(a.iter().map(|x| x.as_ref()))
                .left()
                .map(|x| x.clone())
                .collect::<Vec<i32>>(),
            vec![0, 2, 4]
        );
        assert_eq!(
            IterChoice::new(a.iter().map(|x| x.as_ref()))
                .right()
                .map(|x| x.clone())
                .collect::<Vec<i32>>(),
            vec![1, 3]
        );
        assert_eq!(a.clone().left(), vec![0, 2, 4]);
        assert_eq!(a.right(), vec![1, 3]);
    }

    #[test]
    fn test_factor_distribute() {
        assert_eq!(
            Either::<i32, i32>::factor(std::convert::identity).left()(0),
            Either::Left(0)
        );
        assert_eq!(
            Either::<i32, i32>::factor(std::convert::identity).right()(1),
            Either::Right(1)
        );
        assert_eq!(
            Either::<i32, i32>::distribute(Either::<i32, i32>::factor(std::convert::identity))(
                Either::Left(0)
            ),
            Either::Left(0)
        );
        assert_eq!(
            Either::<i32, i32>::distribute(Either::<i32, i32>::factor(std::convert::identity))(
                Either::Right(1)
            ),
            Either::Right(1)
        );
    }
}

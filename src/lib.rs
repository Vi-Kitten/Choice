pub mod derivatives;
use derivatives::*;

/// Dynamism bootstrapper for Choice
pub trait DynChoice<A, B> {
    /// Convert into `A`
    fn into_left(self: Box<Self>) -> A;

    /// Convert into `B`
    fn into_right(self: Box<Self>) -> B;
}

/// Represents the affine negation of `Either`.
///
/// It represents a conjunctive union.
pub trait Choice<A, B>: DynChoice<A, B> + Sized {
    /// Convert into `A`
    fn left(self: Self) -> A;
    /// Convert into `B`
    fn right(self: Self) -> B;

    /// Maps the left value.
    ///
    /// This treats Choice as a functor in the left type.
    fn map_left<C, F: FnOnce(A) -> C>(
        self,
        left: F,
    ) -> ChooseMap<Self, Both<F, fn(B) -> B>, A, B, F, fn(B) -> B> {
        self.map_both(left, std::convert::identity)
    }

    /// Maps the right value.
    ///
    /// This treats Choice as a functor in the right type.
    fn map_right<C, G: FnOnce(B) -> C>(
        self,
        right: G,
    ) -> ChooseMap<Self, Both<fn(A) -> A, G>, A, B, fn(A) -> A, G> {
        self.map_both(std::convert::identity, right)
    }

    /// Maps both values.
    ///
    /// This treats Choice as a functor in both the left and right types.
    fn map_both<C, D, F: FnOnce(A) -> C, G: FnOnce(B) -> D>(
        self,
        left: F,
        right: G,
    ) -> ChooseMap<Self, Both<F, G>, A, B, F, G> {
        self.choose_map(Both::new(left, right))
    }

    /// Composes a choice of values with a choice of functions to produce a choice of values.
    ///
    /// This sequences the choices in a way that is unique to the structure of a choice.
    fn choose_map<U: Choice<F, G>, C, D, F: FnOnce(A) -> C, G: FnOnce(B) -> D>(
        self,
        choice: U,
    ) -> ChooseMap<Self, U, A, B, F, G> {
        ChooseMap {
            choice: self,
            other: choice,
            _l: std::marker::PhantomData,
            _r: std::marker::PhantomData,
            _f: std::marker::PhantomData,
            _g: std::marker::PhantomData,
        }
    }

    /// Sets the left value to a map from the current state to be ran if chosen.
    ///
    /// This treats Choice as a co-monad in the left type.
    fn cobind_left<C, F: FnOnce(Self) -> C>(self, left: F) -> LeftCoBind<Self, A, F> {
        LeftCoBind {
            choice: self,
            cobind: left,
            _l: std::marker::PhantomData,
        }
    }

    /// Sets the right value to a map from the current state to be ran if chosen.
    ///
    /// This treats Choice as a co-monad in the right type.
    fn cobind_right<C, G: FnOnce(Self) -> C>(self, right: G) -> RightCoBind<Self, A, G> {
        RightCoBind {
            choice: self,
            cobind: right,
            _r: std::marker::PhantomData,
        }
    }

    /// Swaps the left and right values.
    fn swap(self) -> Swap<Self> {
        Swap { choice: self }
    }

    /// Composes a choice of values with an either of functions to produce a single value.
    ///
    /// The composition of a choice with its linear negative annihilates both.
    fn choose<C, F: FnOnce(A) -> C, G: FnOnce(B) -> C>(self, either: Either<F, G>) -> C {
        match either {
            Either::Left(f) => (f)(self.left()),
            Either::Right(g) => (g)(self.right()),
        }
    }
}

impl<A, B> DynChoice<A, B> for Box<dyn DynChoice<A, B>> {
    fn into_left(self: Box<Self>) -> A {
        (*self).into_left()
    }

    fn into_right(self: Box<Self>) -> B {
        (*self).into_right()
    }
}

impl<I: Iterator<Item = Either<A, B>>, A, B>
    DynChoice<LeftFilterIter<I, A, B>, RightFilterIter<I, A, B>> for I
{
    /// Create an iterator that filters for left.
    fn into_left(self: Box<Self>) -> LeftFilterIter<I, A, B> {
        LeftFilterIter {
            iter: *self,
            _l: std::marker::PhantomData,
            _r: std::marker::PhantomData,
        }
    }

    /// Create an iterator that filters for right.
    fn into_right(self: Box<Self>) -> RightFilterIter<I, A, B> {
        RightFilterIter {
            iter: *self,
            _l: std::marker::PhantomData,
            _r: std::marker::PhantomData,
        }
    }
}

impl<A, B> DynChoice<Vec<A>, Vec<B>> for Vec<Either<A, B>> {
    fn into_left(self: Box<Self>) -> Vec<A> {
        (*self).into_iter().left().collect()
    }

    fn into_right(self: Box<Self>) -> Vec<B> {
        (*self).into_iter().right().collect()
    }
}

impl<A, B> DynChoice<Box<[A]>, Box<[B]>> for Box<[Either<A, B>]> {
    fn into_left(self: Box<Self>) -> Box<[A]> {
        (*self).into_vec().left().into_boxed_slice()
    }

    fn into_right(self: Box<Self>) -> Box<[B]> {
        (*self).into_vec().right().into_boxed_slice()
    }
}

impl<T, A, B> Choice<A, B> for T
where
    T: DynChoice<A, B> + Sized,
{
    fn left(self: Self) -> A {
        Box::new(self).into_left()
    }

    fn right(self: Self) -> B {
        Box::new(self).into_right()
    }
}

/// Stores a DynChoice with indirection so that Choice can be implemented
pub struct BoxedChoice<C: ?Sized> {
    choice: Box<C>,
}

impl<C: ?Sized> BoxedChoice<C> {
    pub fn new(choice: Box<C>) -> BoxedChoice<C> {
        BoxedChoice { choice }
    }
}

impl<A, B, C: ?Sized + DynChoice<A, B>> DynChoice<A, B> for BoxedChoice<C> {
    fn into_left(self: Box<Self>) -> A {
        self.choice.into_left()
    }

    fn into_right(self: Box<Self>) -> B {
        self.choice.into_right()
    }
}

/// A choice with both branches identical.
pub struct Same<A> {
    val: A,
}

impl<A> Same<A> {
    /// Constructs a choice with both branches identical.
    pub fn new(val: A) -> Same<A> {
        Same { val }
    }
}

impl<A> DynChoice<A, A> for Same<A> {
    fn into_left(self: Box<Self>) -> A {
        self.val
    }

    fn into_right(self: Box<Self>) -> A {
        self.val
    }
}

/// A choice with both branches already inhabited.
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

impl<A, B> DynChoice<A, B> for Both<A, B> {
    fn into_left(self: Box<Self>) -> A {
        self.left
    }

    fn into_right(self: Box<Self>) -> B {
        self.right
    }
}

/// A choice using with lazy expressions.
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

impl<A, B, F: FnOnce() -> A, G: FnOnce() -> B> DynChoice<A, B> for Lazy<A, B, F, G> {
    fn into_left(self: Box<Self>) -> A {
        (self.left)()
    }

    fn into_right(self: Box<Self>) -> B {
        (self.right)()
    }
}

/// A choice with a common resource.
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

impl<T, A, B, F: FnOnce(T) -> A, G: FnOnce(T) -> B> DynChoice<A, B> for Exclusive<T, F, G> {
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
    pub fn left_from(result: Result<A, B>) -> Either<A, B> {
        result.map_or_else(Either::Right, Either::Left)
    }

    /// Sets the right branch from a result assuming `Ok`, otherwise if `Err` sets the left branch instead.
    pub fn right_from(result: Result<B, A>) -> Either<A, B> {
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

    /// Composes an either with a choice of functions to produce an either of results.
    ///
    /// This sequences the either and choice in a way that is unique to their structures.
    pub fn choose_map<C, D, F: FnOnce(A) -> C, G: FnOnce(B) -> D>(
        self,
        choice: impl Choice<F, G>,
    ) -> Either<C, D> {
        match self {
            Either::Left(a) => Either::Left((choice.left())(a)),
            Either::Right(b) => Either::Right((choice.right())(b)),
        }
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
        choice: impl Choice<F, G>,
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
        choice: impl Choice<F, G>,
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
pub mod test {
    use super::*;
}

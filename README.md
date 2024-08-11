# Choice

An implementation of affine addative conjunction in the rust type system.

This can be used to group mutually exclusive function parameters so that they can have overlapping captures.

## Usage

The following code using `Result` does not work as it

```rs
Ok(0)
    .map(|x: i32| sender.send(x + 1))
    .map_err(|y: i32| sender.send(y - 1));
//!          ^^^^^^^^ use of moved value: `sender`
```

Whereas using `Either` and passing a `Choice` of two functions circumvents this issues by storing the two branches in the same object.

```rs
Either::Left(0).choose_map(Exclusive::new(
    sender,
    |s| move |x: i32| s.send(x + 1),
    |s| move |y: i32| s.send(y - 1),
));
```

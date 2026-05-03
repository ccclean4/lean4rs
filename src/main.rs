mod level;
mod expr;
mod kernel;
mod elaborator;
mod parser;

use elaborator::Elaborator;
use parser::run_script;

fn main() {
    let mut elab = Elaborator::new();

    // ---- Bool ------------------------------------------------
    run_script(r#"
        inductive Bool : Prop where
          | Bool.true  : Bool
          | Bool.false : Bool

        def not : Bool -> Bool :=
          fun (b : Bool) =>
            match b with
            | Bool.true  => Bool.false
            | Bool.false => Bool.true

        #eval not Bool.true
        #eval not Bool.false
        #check not
    "#, &mut elab);

    // ---- Nat ------------------------------------------------
    run_script(r#"
        inductive Nat : Type where
          | Nat.zero : Nat
          | Nat.succ : Nat -> Nat

        #eval 0
        #eval 3

        def add : Nat -> Nat -> Nat :=
          fix add_fn : Nat -> Nat -> Nat =>
            fun (n : Nat) => fun (m : Nat) =>
              match n with
              | Nat.zero        => m
              | Nat.succ n_prev => Nat.succ (add_fn n_prev m)

        #eval add 2 3
        #check add

        def mul : Nat -> Nat -> Nat :=
          fix mul_fn : Nat -> Nat -> Nat =>
            fun (n : Nat) => fun (m : Nat) =>
              match n with
              | Nat.zero        => 0
              | Nat.succ n_prev => add m (mul_fn n_prev m)

        #eval mul 3 4
    "#, &mut elab);

    // ---- Polymorphic identity with universe params -----------
    run_script(r#"
        def id.{u} : {α : Sort u} -> α -> α :=
          fun {α : Sort u} => fun (x : α) => x

        #eval id 42
        #eval id Bool.true
        #check id
    "#, &mut elab);

    // ---- Polymorphic List ------------------------------------
    run_script(r#"
        inductive List.{u} : {α : Sort u} -> Type where
          | List.nil  : {α : Sort u} -> List α
          | List.cons : {α : Sort u} -> α -> List α -> List α

        def List.length.{u} : {α : Sort u} -> List α -> Nat :=
          fun {α : Sort u} => fun (xs : List α) =>
            match xs with
            | List.nil          => 0
            | List.cons _ t => Nat.succ (List.length t)

        #eval List.length (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))
    "#, &mut elab);
}
-- Mario Carneiro found this bug.
-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Soundness.20bug.3A.20hasLooseBVars.20is.20not.20conservative/near/521286338
import Lean
open Lean

def isProp.{u} : Prop :=
  ∀ (x : Sort u) (y z : x), y = z

theorem isProp_prop : isProp.{0} :=
  fun _ _ _ => rfl

theorem not_isProp_type : ¬ isProp.{1} :=
  fun h => nomatch h _ 0 1

theorem isProp_not_invariant : isProp.{0} ≠ isProp.{1} :=
  mt (fun h => cast h isProp_prop) not_isProp_type

def mkLevel : Nat → Level → Level
| 0, e => e
| Nat.succ n, e => mkLevel n (.max .zero e)

open Lean Elab Command

elab "add_magic" : command => do
  let l := mkLevel (2^24) (.param `u)

  liftCoreM <|
    Lean.addDecl <|
      Declaration.defnDecl {
        name := `magic
        levelParams := []
        type := Expr.sort Level.zero
        value := Expr.const `isProp [l]
        hints := ReducibilityHints.opaque
        safety := DefinitionSafety.safe
      }

add_magic

elab "add_magic_eq" : command => do
  liftCoreM do
    Lean.addDecl <|
      Declaration.defnDecl {
        toConstantVal := {
          name := `magic_eq
          levelParams := [`u]
          type :=
            mkApp3
              (mkConst ``Eq [levelOne])
              (Expr.sort Level.zero)
              (Expr.const `magic [])
              (Expr.const `isProp [.param `u])
        }
        value :=
          mkApp2
            (mkConst ``Eq.refl [levelOne])
            (Expr.sort Level.zero)
            (Expr.const `magic [])
        hints := ReducibilityHints.opaque
        safety := DefinitionSafety.safe
        all := [`magic_eq]
      }

add_magic_eq

universe u

example : magic = isProp.{u} :=
  magic_eq.{u}

theorem contradiction : False :=
  isProp_not_invariant
    (magic_eq.{0}.symm.trans magic_eq.{1})

#print axioms contradiction

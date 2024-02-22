namespace wkmath

/- uses base 3 -/
inductive Digit
  | zero
  | one
  | two

notation:1025 " (0) " => Digit.zero
notation:1025 " (1) " => Digit.one
notation:1025 " (2) " => Digit.two

namespace Digit

def toString:Digit → String
  | zero => "0"
  | one => "1"
  | two => "2"

def toNat:Digit → Nat
  | (0) => 0
  | (1) => 1
  | (2) => 2

theorem toNat_le_2{d:Digit}:d.toNat ≤ 2:=
  match d with
  | (0) | (1) | (2) => by simp

theorem toNat_lt_3{d:Digit}:d.toNat < 3:=
  match d with
  | (0) | (1) | (2) => by simp

theorem eq_iff_toNat_eq{a b:Digit}:a = b ↔ a.toNat = b.toNat:=
  match a, b with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => by simp

@[inline] instance : ToString Digit where
  toString := toString

@[inline] instance instDecidableEq{a b:Digit} : Decidable (a=b) :=
  match a,b with
  | zero, zero
  | one, one
  | two, two => isTrue rfl
  | zero, one
  | zero, two
  | one, zero
  | one, two
  | two, zero
  | two, one => isFalse (fun h => Digit.noConfusion h)

@[inline] instance instDecidableEqInst:DecidableEq Digit:=
  λ _ _ => instDecidableEq

end Digit

inductive Digits
  | nil
  | cons : Digits → Digit → Digits

notation:1025 " ε " => Digits.nil
infixl:67 " :: " => Digits.cons

namespace Digits

def toString:Digits → String
  | ε => ""
  | ds::d => ds.toString ++ d.toString

@[inline] instance : ToString Digits where
  toString := toString

@[inline] instance instDecidableEq{x y:Digits}:Decidable (x = y):=
  match x, y with
  | ε, _::_
  | _::_, ε => isFalse (fun h => Digits.noConfusion h)
  | ε, ε => isTrue rfl
  | x'::xt, y'::yt => by{
    simp
    have : Decidable (x' = y') := instDecidableEq
    have : Decidable (xt = yt) := Digit.instDecidableEq
    exact instDecidableAnd
  }

theorem not_ε_exists_cons{x:Digits}(h:x ≠ ε):∃(x':Digits)(d:Digit), x = x'::d:=by{
  match x with
  | ε => contradiction
  | x'::d => exact ⟨x', d, rfl⟩
}

end Digits

end wkmath

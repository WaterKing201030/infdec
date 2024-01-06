namespace wkmath

/- uses base 3 -/
inductive Digit
  | zero
  | one
  | two

namespace Digit

def toString:Digit → String
  | zero => "0"
  | one => "1"
  | two => "2"

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

end Digit

inductive Digits
  | nil
  | cons : Digits → Digit → Digits

notation:1025 " ε " => Digits.nil
infixr:67 " :: " => Digits.cons

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

end Digits

end wkmath

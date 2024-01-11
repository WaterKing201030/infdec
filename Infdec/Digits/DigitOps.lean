import Infdec.Digits.Base

namespace wkmath
namespace Digit
def lt:Digit → Digit → Prop
  | (0), (1)
  | (0), (2)
  | (1), (2) => True
  | (0), (0)
  | (1), (0)
  | (1), (1)
  | (2), (0)
  | (2), (1)
  | (2), (2) => False

def le:Digit → Digit → Prop
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (1)
  | (1), (2)
  | (2), (2) => True
  | (1), (0)
  | (2), (0)
  | (2), (1) => False

infix:50 " ≤ " => le
infix:50 " < " => lt

section order_properties
@[inline] instance le.instDecidable{x y:Digit}:Decidable (x ≤ y):=
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (1)
  | (1), (2)
  | (2), (2) => instDecidableTrue
  | (1), (0)
  | (2), (0)
  | (2), (1) => instDecidableFalse

@[inline] instance lt.instDecidable{x y:Digit}:Decidable (x < y):=
  match x, y with
  | (0), (1)
  | (0), (2)
  | (1), (2) => instDecidableTrue
  | (0), (0)
  | (1), (0)
  | (1), (1)
  | (2), (0)
  | (2), (1)
  | (2), (2) => instDecidableFalse

theorem le.refl(x:Digit):x ≤ x:=by{
  match x with
  | (0)
  | (1)
  | (2) => simp[le]
}

theorem lt.irrefl(x:Digit):¬x < x:=by{
  match x with
  | (0)
  | (1)
  | (2) => simp[lt]
}

theorem le.antisymm{x y:Digit}(h0:x ≤ y)(h1: y ≤ x):x=y:=by{
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => simp[le] at *
}

theorem lt.asymm{x y:Digit}(h:x < y):¬y < x:=by{
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => simp[lt] at *
}

theorem le.trans{x y z:Digit}(h0:x ≤ y)(h1:y ≤ z):x ≤ z:=by{
  match x, y, z with
  |(0), (0), (0)
  |(0), (0), (1)
  |(0), (0), (2)
  |(0), (1), (0)
  |(0), (1), (1)
  |(0), (1), (2)
  |(0), (2), (0)
  |(0), (2), (1)
  |(0), (2), (2)
  |(1), (0), (0)
  |(1), (0), (1)
  |(1), (0), (2)
  |(1), (1), (0)
  |(1), (1), (1)
  |(1), (1), (2)
  |(1), (2), (0)
  |(1), (2), (1)
  |(1), (2), (2)
  |(2), (0), (0)
  |(2), (0), (1)
  |(2), (0), (2)
  |(2), (1), (0)
  |(2), (1), (1)
  |(2), (1), (2)
  |(2), (2), (0)
  |(2), (2), (1)
  |(2), (2), (2) => simp[le] at *
}

theorem lt.trans{x y z:Digit}(h0:x < y)(h1:y < z):x < z:=by{
  match x, y, z with
  |(0), (0), (0)
  |(0), (0), (1)
  |(0), (0), (2)
  |(0), (1), (0)
  |(0), (1), (1)
  |(0), (1), (2)
  |(0), (2), (0)
  |(0), (2), (1)
  |(0), (2), (2)
  |(1), (0), (0)
  |(1), (0), (1)
  |(1), (0), (2)
  |(1), (1), (0)
  |(1), (1), (1)
  |(1), (1), (2)
  |(1), (2), (0)
  |(1), (2), (1)
  |(1), (2), (2)
  |(2), (0), (0)
  |(2), (0), (1)
  |(2), (0), (2)
  |(2), (1), (0)
  |(2), (1), (1)
  |(2), (1), (2)
  |(2), (2), (0)
  |(2), (2), (1)
  |(2), (2), (2) => simp[lt] at *
}

theorem lt_of_le_of_ne{x y:Digit}(h0:x ≤ y)(h1:x ≠ y):x < y:=by{
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => simp[lt,le] at *
}

theorem lt.to_le{x y:Digit}(h:x < y):x ≤ y:=by{
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => simp[lt,le] at *
}

theorem le.to_eq_or_lt{x y:Digit}(h:x ≤ y):x = y ∨ x < y:=by{
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => simp[lt,le] at *
}

theorem lt.to_ne{x y:Digit}(h:x < y):x ≠ y:=by{
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => simp[lt] at *
}

theorem lt.to_not_ge{x y:Digit}(h:x < y):¬y ≤ x:=by{
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => simp[lt,le] at *
}

theorem lt_of_not_ge{x y:Digit}(h:¬x ≤ y):y < x:=by{
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => simp[lt,le] at *
}

theorem lt_iff_not_ge{x y:Digit}:x < y ↔ ¬y ≤ x:=
  Iff.intro lt.to_not_ge lt_of_not_ge

theorem le.to_not_gt{x y:Digit}(h:x ≤ y):¬y < x:=by{
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => simp[lt,le] at *
}

theorem le_of_not_gt{x y:Digit}(h:¬x < y):y ≤ x:=by{
  match x, y with
  | (0), (0)
  | (0), (1)
  | (0), (2)
  | (1), (0)
  | (1), (1)
  | (1), (2)
  | (2), (0)
  | (2), (1)
  | (2), (2) => simp[lt,le] at *
}

theorem le_iff_not_gt{x y:Digit}:x ≤ y ↔ ¬y < x:=
  Iff.intro le.to_not_gt le_of_not_gt

theorem zero_le(x:Digit):(0) ≤ x:=by{
  match x with
  | (0)
  | (1)
  | (2) => simp[lt]
}

theorem not_lt_zero(x:Digit):¬x < (0):=by{
  match x with
  | (0)
  | (1)
  | (2) => simp[lt]
}
end order_properties
end Digit
end wkmath

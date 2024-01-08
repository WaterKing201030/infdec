import Infdec.Digits

namespace wkmath
namespace Digits
def nat.eq:Digits → Digits → Prop
  | ε, ε => True
  | ε, ds::d
  | ds::d, ε => (ds::d).isZero
  | xs::xd, ys::yd => eq xs ys ∧ xd = yd

notation:50 lhs:51 " =N " rhs:51 => nat.eq lhs rhs

@[inline] instance nat.eq.instDecidable{x y:Digits}:Decidable (x=Ny):=
  match x, y with
  | ε, ε => instDecidableTrue
  | ε, _::_
  | _::_, ε => isZero.instDecidable
  | x::_, y::_ =>
    have : Decidable (x =N y):=instDecidable
    instDecidableAnd

theorem zero_nat_eq_zero{x y:Digits}(hx:x.isZero)(hy:y.isZero):x =N y:=by{
  cases x with
  | nil => cases y with
    | nil => simp[nat.eq]
    | cons ys yd => simp[nat.eq];exact hy
  | cons xs xd => cases y with
    | nil => simp[nat.eq]; exact hx
    | cons ys yd => simp[nat.eq]; simp[isZero] at *;exact And.intro (zero_nat_eq_zero hx.left hy.left) (hx.right.trans hy.right.symm)
}

theorem nat.eq.refl(x:Digits):x =N x:=by{
  induction x with
  | nil => simp[eq]
  | cons xs xd ih => simp[eq]; exact ih
}

theorem nat.eq.symm{x y:Digits}(h:x =N y):y =N x:=by{
  match x, y with
  | ε, ε => simp[eq]
  | ε, ds::d
  | ds::d, ε => simp[eq] at *;exact h
  | xs::xd, ys::yd => simp[eq] at *; exact And.intro h.left.symm h.right.symm
}

theorem nat_eq_zero_isZero{x y:Digits}(h:x =N y)(hx:x.isZero):y.isZero:=by{
  match x, y with
  | _, ε => simp[isZero]
  | ε, _::_ => simp[nat.eq] at h; exact h
  | xs::xd, ys::yd => {
    rw[isZero] at hx
    rw[nat.eq] at h
    rw[hx.right] at h
    rw[←h.right]
    simp[isZero]
    exact nat_eq_zero_isZero h.left hx.left
  }
}

theorem nat_eq_zero_isZero'{x y:Digits}(h:x =N y)(hy:y.isZero):x.isZero:=
  nat_eq_zero_isZero h.symm hy

theorem nat.eq.trans{x y z:Digits}(h0:x =N y)(h1:y =N z):x =N z:=by{
  match x, y, z with
  | ε, _, _ => {
    exact zero_nat_eq_zero ε_isZero (nat_eq_zero_isZero h1 (nat_eq_zero_isZero h0 ε_isZero))
  }
  | _::_, ε, _ => {
    exact zero_nat_eq_zero (nat_eq_zero_isZero' h0 ε_isZero) (nat_eq_zero_isZero h1 ε_isZero)
  }
  | _::_, _::_, ε => {
    exact zero_nat_eq_zero (nat_eq_zero_isZero' h0 (nat_eq_zero_isZero' h1 ε_isZero)) ε_isZero
  }
  | _::_, _::_, _::_ => {
    simp[eq] at *
    exact And.intro (h0.left.trans h1.left) (h0.right.trans h1.right)
  }
}

end Digits
end wkmath

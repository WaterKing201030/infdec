import Infdec.Cycdec.Base

namespace wkmath
class Frac where
  num: Nat
  den: Nat
  inv: den ≠ 0

namespace Frac
def eq(x y:Frac):=
  x.den * y.num = x.num * y.den
notation:50 lhs:51 " =F " rhs:51 => eq lhs rhs

def mul(x y:Frac):Frac:=
  ⟨x.num * y.num, x.den * y.den, Nat.mul_ne_zero x.inv y.inv⟩

infixl:70 " * " => mul

def ofNat(x:Nat):Frac:=
  ⟨x, 1, Nat.noConfusion⟩
end Frac

namespace cyc
def toFrac(x:cyc):Frac:=
  if x.exp.negsign then
    ⟨x.pre.toNat * x.post.toNegOne.toNat + x.post.toNat, (x.post.toNegOne ++ x.exp.digits.toOneBaseNat).toNat, λ h => Digits.not_zero_append_isNotZero (Digits.not_ε_toNegOne_not_zero x.inv) (Digits.isZero_iff_toNat_eq_zero.mpr h)
    ⟩
  else
    ⟨((x.pre * x.post.toNegOne + x.post) ++ x.exp.digits.toOneBaseNat).toNat, x.post.toNegOne.toNat, λ h => Digits.not_ε_toNegOne_not_zero x.inv (Digits.isZero_iff_toNat_eq_zero.mpr h)⟩

theorem toFrac_fraceq_of_cyc_eq{x y:cyc}(h:x =C y):x.toFrac =F y.toFrac:=by{
  
}
end cyc
end wkmath

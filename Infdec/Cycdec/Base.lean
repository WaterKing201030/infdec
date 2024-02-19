import Infdec.Integer
namespace wkmath
class cyc where
  pre:Digits
  post:Digits
  exp:int
  inv:post ≠ ε

namespace cyc
axiom eq:cyc → cyc → Prop
notation:50 lhs:51 " =C " rhs:51 => eq lhs rhs

axiom eq.refl'{a b x y:Digits}{i j:int}:a =N b → x = y → i =I j → (h:x ≠ ε) → (h':y ≠ ε) → ⟨a, x, i, h⟩ =C ⟨b, y, j, h'⟩
axiom eq.symm{x y:cyc}:x =C y → y =C x
axiom eq.trans{x y z:cyc}:x =C y → y =C z → x =C z
axiom eq.movr{d:Digit}{a x:Digits}{i:int}:⟨a::d, x::d, i, Digits.noConfusion⟩ =C ⟨a, (ε::d)++x, i + int.One, Digits.not_ε_append Digits.noConfusion x⟩
axiom eq.mincyc:∀{a x:Digits}{i:int}{h:x ≠ ε}, ⟨a, x, i, h⟩ =C ⟨a, x.minCyc, i, Digits.not_ε_minCyc_not_ε h⟩

theorem eq.refl(x:cyc):x =C x:=
  refl' (Digits.nat.eq.refl _) rfl (int.eq.refl _) x.inv x.inv
theorem eq.symm_iff{x y:cyc}:x =C y ↔ y =C x:=
  Iff.intro symm symm
theorem eq.movl{d:Digit}{a x:Digits}{i:int}:⟨a::d, x::d, i - int.One, Digits.noConfusion⟩ =C ⟨a, (ε::d)++x, i, Digits.not_ε_append Digits.noConfusion x⟩:=by{
  apply movr.trans
  apply refl' (Digits.nat.eq.refl _) (Eq.refl _)
  rw[int.sub]
  apply (int.add.assoc _ _ _).trans
  have h'':(-int.One + int.One).isZero:=by simp[int.One, int.neg, int.add, Digits.sub, Digits.half_sub, Digits.half_sub', Digit.half_sub3, int.isZero]
  exact int.add_zero i h''
}

end cyc
end wkmath

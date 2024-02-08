import Infdec.Integer

namespace wkmath
class cyc where
  pre:Digits
  post:Digits
  exp:int

namespace cyc
axiom eq:cyc → cyc → Prop
notation:50 lhs:51 " =C " rhs:51 => eq lhs rhs

axiom eq.refl'{a b x y:Digits}{i j:int}:a =N b → x = y → i =I j → ⟨a, x, i⟩ =C ⟨b, y, j⟩
axiom eq.symm{x y:cyc}:x =C y → y =C x
axiom eq.trans{x y z:cyc}:x =C y → y =C z → x =C z
axiom eq.movr{d:Digit}{a x:Digits}{i:int}:⟨a::d, x::d, i⟩ =C ⟨a, (ε::d)++x, i + int.One⟩
axiom eq.mincyc:∀{a x:Digits}{i:int}, ⟨a, x, i⟩ =C ⟨a, x.minCyc, i⟩

theorem eq.refl(x:cyc):x =C x:=
  refl' (Digits.nat.eq.refl _) rfl (int.eq.refl _)
theorem eq.symm_iff{x y:cyc}:x =C y ↔ y =C x:=
  Iff.intro symm symm
theorem eq.movl{d:Digit}{a x:Digits}{i:int}:⟨a::d, x::d, i - int.One⟩ =C ⟨a, (ε::d)++x, i⟩:=by{
  apply movr.trans
  apply refl' (Digits.nat.eq.refl _) (Eq.refl _)
  rw[int.sub]
  apply (int.add.assoc _ _ _).trans
  have h'':(-int.One + int.One).isZero:=by{
    simp[int.One, int.neg, int.add, Digits.sub, Digits.half_sub, Digits.half_sub', Digit.half_sub3, int.isZero]
  }
  exact int.add_zero i h''
}

end cyc
end wkmath

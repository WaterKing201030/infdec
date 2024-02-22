import Infdec.ExtNat

namespace wkmath

structure int where
  digits:Digits
  negsign:Bool

namespace int
def ofnat(x:Digits):int:=
  ⟨x,false⟩

def neg:int → int
  | ⟨x,false⟩ => ⟨x,true⟩
  | ⟨x,true⟩ => ⟨x,false⟩

prefix:75 "-"    => neg

def neg.inv{x:int}:-(-x) = x:=
  match x with | ⟨_,false⟩ | ⟨_, true⟩ => rfl

def isZero(x:int):=
  x.digits.isZero

@[inline] instance isZero.instDecidable{x:int}:Decidable (isZero x):=
  Digits.isZero.instDecidable

def Zero:int:=⟨ε, false⟩
def One:int:=⟨ε::(1), false⟩
def NegOne:int:=⟨ε::(1), true⟩

def toStdInt(x:int):int:=
  match x with
  | ⟨s,b⟩ =>
    if s.isZero then
      ⟨ε, false⟩
    else
      ⟨s.toStdNat, b⟩

def isZero_iff_toStdInt_zero(x:int):x.isZero ↔ x.toStdInt = ⟨ε,false⟩:=by{
  match x with
  | ⟨x0, x1⟩ => {
    apply Iff.intro
    . {
      intro h
      simp[isZero] at h
      simp[toStdInt, h]
    }
    . {
      intro h
      simp[isZero]
      simp[toStdInt] at h
      cases Decidable.em (x0.isZero) with
      | inl h' => exact h'
      | inr h' => {
        simp[h'] at h
        exact Digits.toStdNat_ε_isZero h.left
      }
    }
  }
}
end int

def Digits.to_int(x:Digits):int:=⟨x, false⟩

end wkmath

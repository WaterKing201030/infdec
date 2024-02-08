import Infdec.ExtNat

namespace wkmath

class int where
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
end int

def Digits.to_int(x:Digits):int:=⟨x, false⟩

end wkmath

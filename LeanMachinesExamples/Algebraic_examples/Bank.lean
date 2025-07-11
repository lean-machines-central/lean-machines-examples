import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Ordinary
import LeanMachines.Event.Algebra.Ordinary



structure Dollar where
  val : Nat

structure Euro where
  val : Nat


instance : HAdd Euro Euro Euro where
  hAdd e₁ e₂ := Euro.mk (e₁.val + e₂.val)

def Euro.change := 116
def Dollar.change := 86

def Euro.toDollar (e : Euro) :=
  Dollar.mk (e.val * Euro.change)

def Dollar.toEuro (d : Dollar) :=
  Euro.mk (d.val * Dollar.change)


structure BankAccount where
  sold : Euro
structure BankCTX where

instance : Machine BankCTX BankAccount where
  context := {}
  default := {sold := (Euro.mk 0)}
  invariant m := True


def BankAccount.Init : InitEvent BankAccount Unit Unit :=
  newInitEvent''
  {
    init _ := {sold := (Euro.mk 0)}
    safety grd :=
      by
        simp[Machine.invariant]

  }

def BankAccount.Put : OrdinaryEvent BankAccount Euro Unit :=
  newEvent'
  {
    action m e _ := {m with sold := m.sold + e}
    safety := by simp[Machine.invariant]
  }


def BankAccount.Get : OrdinaryEvent BankAccount Euro Euro :=
  newEvent
  {
    guard m v := m.sold.val - v.val > 0
    action m v _ := (v,{m with sold := Euro.mk (m.sold.val - v.val)})
    safety := by simp[Machine.invariant]
  }

def BankAccount.Get_D : OrdinaryEvent BankAccount Dollar Dollar :=
  Profunctor.dimap Dollar.toEuro Euro.toDollar BankAccount.Get

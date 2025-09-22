import EvmYul.Yul.State

namespace EvmYul

namespace Yul

inductive Exception where
  | YulHalt (state : Yul.State) (value : UInt256) : Exception
  -- | StopInvoked        : Exception

instance : Repr Exception where
  reprPrec s _ :=
    match s with
      | .InvalidArguments => "InvalidArguments"
      | .NotEncodableRLP => "NotEncodableRLP"
      | .InvalidInstruction => "InvalidInstruction"
      | .OutOfFuel => "OutOfFuel"
      | .StaticModeViolation => "StaticModeViolation"
      | .MissingContract => "MissingContract"
      | .MissingContractFunction => "MissingContractFunction"
      | .InvalidExpression => "InvalidExpression"
      | .YulHalt _ _ => "YulHalt: (holds a state and a value)"


end Yul

end EvmYul

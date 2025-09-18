namespace EvmYul

namespace Yul

inductive Exception where
  | InvalidArguments        : Exception
  | NotEncodableRLP         : Exception
  | InvalidInstruction      : Exception
  | OutOfFuel               : Exception
  | StaticModeViolation     : Exception
  | MissingContract         : Exception
  | MissingContractFunction : Exception
  | InvalidExpression       : Exception
  -- | StopInvoked        : Exception

end Yul

end EvmYul

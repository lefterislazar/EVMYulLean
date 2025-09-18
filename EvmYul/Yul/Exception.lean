namespace EvmYul

namespace Yul

inductive Exception where
  | InvalidArguments   : Exception
  | NotEncodableRLP    : Exception
  | InvalidInstruction : Exception
  | OutOfFuel          : Exception
  -- | StopInvoked        : Exception

end Yul

end EvmYul

`safe-access` is a small Haskell library to control accesses through a simple capability-based interface.

# Concepts

## Access descriptor

You will have to define a type describing the different kind of accesses that your program will be performing.

## Capability

A capability describes some accesses that are granted or denied for a certain part of your program or another subsystem. It simply is a function from an access descriptor to an access decision explained thereafter.

## Access decision

Every capability can return a decision. `AccessGranted` and `AccessDenied` are pretty obvious while `AccessDeniedSoft` would deny the access should no other capability overwrite this decision.

## SafeAccessT

`SafeAccessT` is a monad transformer in which you can run some piece of code and check for accesses. It also instantiates `Applicative`, `Functor` and `MonadIO` with the appropriate conditions.

# Example

    import Control.Applicative
    import Control.SafeAccess

    data Descr = AccessA | AccessB | OtherDescr String deriving (Show, Eq)

    instance AccessDescriptor Descr where
      descrMsg = OtherDescr -- this is for the function fail in Monad

    normalUserCapability :: Capability Descr
    normalUserCapability = MkCapability $ \descr -> case descr of
      AccessA -> AccessGranted
      AccessB -> AccessDenied
      _       -> AccessDeniedSoft

    getA :: SafeAccessT Descr IO String
    getA = do
      ensureAccess AccessA
      return "A"

    getB :: SafeAccessT Descr IO String
    getB = do
      ensureAccess AccessB
      return "B"

    getData :: SafeAccessT Descr IO (String, String)
    getData = (,) <$> getA <*> getB

    main :: IO ()
    main = do
      eRes <- runSafeAccessT getData [normalUserCapability]
      print eRes -- will print Left AccessB
module Lib.RawString (r) where

import Language.Haskell.TH
import Language.Haskell.TH.Quote

r :: QuasiQuoter 
r = QuasiQuoter {
    quoteExp = return . LitE . StringL
    , quotePat = const (fail "only raw strings literals allowed in a raw string literal quote")
    , quoteType = const (fail "only raw strings literals allowed in a raw string literal quote")
    , quoteDec = const (fail "only raw strings literals allowed in a raw string literal quote")
}


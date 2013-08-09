definition module Tonic.TonicAG

from Control.Monad.Identity import :: Identity (..)
from syntax import :: Expression

:: Expressions  :== [ Expression ]

wrap_Expressions :: T_Expressions  Inh_Expressions  -> (Syn_Expressions )
sem_Expressions :: Expressions  -> T_Expressions 

:: T_Expressions  = T_Expressions (Identity (T_Expressions_s5 ))
:: T_Expressions_s5  = C_Expressions_s5 (T_Expressions_v4 )
:: T_Expressions_s6  = C_Expressions_s6
:: T_Expressions_v4  :== (T_Expressions_vIn4 ) -> (T_Expressions_vOut4 )
:: T_Expressions_vIn4  = T_Expressions_vIn4 (Int)
:: T_Expressions_vOut4  = T_Expressions_vOut4 (Int)

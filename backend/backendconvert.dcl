definition module backendconvert

from backend import BackEnd
import frontend

backEndConvertModules :: PredefinedSymbols FrontEndSyntaxTree !Int *VarHeap *BackEnd -> (!*VarHeap,!*BackEnd)

definition module backendconvert

from backend import BackEnd
import frontend

backEndConvertModules :: PredefinedSymbols FrontEndSyntaxTree VarHeap *BackEnd -> *BackEnd

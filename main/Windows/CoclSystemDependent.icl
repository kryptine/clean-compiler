// this is for Windows
implementation module CoclSystemDependent

PathSeparator
	:==	';'
DirectorySeparator
	:== '\\'

SystemDependentDevices :: [a]
SystemDependentDevices
		=	[]

SystemDependentInitialIO :: [a]
SystemDependentInitialIO
		=	[]

// this is for Windows
definition module CoclSystemDependent

// RWS split
// from deltaIOSystem import DeviceSystem
// from deltaEventIO import InitialIO, IOState

PathSeparator
	:==	';'
DirectorySeparator
	:== '\\'

SystemDependentDevices :: [a]
SystemDependentInitialIO :: [a]

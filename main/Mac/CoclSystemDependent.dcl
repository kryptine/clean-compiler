// this is for the PowerMac
definition module CoclSystemDependent

from deltaIOSystem import DeviceSystem
from deltaEventIO import InitialIO, IOState

PathSeparator
	:==	','
DirectorySeparator
	:==	':'

SystemDependentDevices :: [DeviceSystem .a (IOState .a)]
SystemDependentInitialIO :: InitialIO *s

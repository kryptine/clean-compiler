implementation module compilerSwitches

switch_import_syntax one_point_three two_point_zero :== two_point_zero
	/* when finally removing this switch also remove the argument of STE_Instance and ID_OldSyntax */

SwitchPreprocessor preprocessor no_preprocessor :== preprocessor

SwitchGenerics on off :== on
SwitchGenericInfo on off :== on

// MV...
// - change T_ypeObjectType in StdDynamic (remove DummyModuleName-argument of T_ypeConsSymbol)
// - the (ModuleID _)-constructor is *not* yet shared

USE_DummyModuleName yes no :== yes

switch_dynamics on off :== on;		// to turn dynamics on or off
// ...MV

definition module set_return_code;

from StdString import String;

:: *UniqueWorld :== World;
set_return_code :: !Int !UniqueWorld -> UniqueWorld;
// void set_return_code (int return_code);

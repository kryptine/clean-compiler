definition module Clean2AppleEventHandler;

from StdString import String;
from StdFile import Files;
from events import Event;

install_apple_event_handlers :: Int;
HandleAppleEvent :: !Event (!{#Char} *Files -> (!Int,!*Files)) !*Files -> (!Bool,!Bool,!*Files);

get_apple_event_string :: !Int !String -> Int;

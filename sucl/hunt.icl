>|| Literal script "hunt.lit"

>   %export
>       findfiles
>       glob
>       readable
>       writable
>       getpath
>       expand

>   %include "basic.lit"

>   findfiles :: ([char]->bool) -> [[char]] -> [[char]] -> [char] -> [[char]]

>   findfiles goodmode exts paths base
>   =   filter (goodmode.filemode) (expand exts paths base)

>   relative :: [char] -> bool
>   relative ('/':cs) = False
>   relative ccs = True

>   expand :: [[char]] -> [[char]] -> [char] -> [[char]]
>   expand exts paths base
>   =   [path++'/':base++ext|path<-mkset paths;ext<-mkset exts], if relative base
>   =   [base++ext|ext<-mkset exts], otherwise

>   readable :: [char] -> bool
>   readable ('d':rwx) = False
>   readable (d:'r':wx) = True
>   readable drwx = False

>   writable :: [char] -> bool
>   writable "" = True
>   writable ('d':rwx) = False
>   writable (d:r:'w':x) = True
>   writable drwx = False

>   getpath :: [[char]] -> [char] -> [[char]]
>   getpath syspath varname
>   =   foldr (fill syspath) [] (split ':' (getenv varname))

>   fill syspath [] = (syspath++)
>   fill syspath = (:)

>   glob :: [char] -> [[char]]
>   glob pattern
>   =   filter (~=[]) ((concat.map (split ' ').lines) stdout), if return=0
>   =   error ("glob: "++stderr), otherwise
>       where (stdout,stderr,return) = system ("echo "++pattern)

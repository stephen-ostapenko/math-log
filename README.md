# HW 2

### Программа

Решение второй домашки. Написано на Python с использованием SAT-решателя Cadical (в переменной `PATH_TO_SAT_SOLVER` необходимо указать путь к исполняемому файлу решателя).

Формат запуска: `./fersat.py <N>`, где `N` -- размер шахматной доски. Если расстановку выполнить невозможно, программа напечатает `Impossible!`. Если возможно, программа напечатает саму расстановку. Примеры:
```
stephen@flaaxBook:~/src/math-log$ ./fersat.py 3

Impossible!

```
```
stephen@flaaxBook:~/src/math-log$ ./fersat.py 8
...#....
......#.
....#...
.#......
.....#..
#.......
..#.....
.......#
```

Ферзи отмечены решётками.

Формула генерируется сразу в КНФ.

### Тесты

Тесты описаны в файле `test.py`. Их можно запускать:
```
stephen@flaaxBook:~/src/math-log$ ./test.py 
Test n = 1: ok
Test n = 2: ok
Test n = 3: ok
Test n = 4: ok
Test n = 5: ok
...
Test n = 50: ok
0 error(s)
```

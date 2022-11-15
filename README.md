# learn halo2 by fibonacci
## Layout
|  row  |   n    |    l     |   r    | n_inv  | instance |
|:-----:|:------:|:--------:|:------:|:------:|:--------:|
|       | Advice |  Advice  | Advice | Advice | Instance |
|   0   |   n    |  fib(0)  | fib(1) |   *    |  fib(0)  |
|   1   |  n-1   |  fib(1)  | fib(2) |   *    |  fib(1)  |
|   2   |  n-2   |  fib(2)  | fib(3) |   *    |     n    |
|   3   |  n-3   |  fib(3)  | fib(4) |   *    |  fib(n)  |
|  ...  |  ...   |   ...    |  ...   |  ...   |    ...   |
|  n-1  |   1    | fib(n-1) | fib(n) |   1    |          |
|   n   |   0    |  fib(n)  | fib(n) |   0    |          |
|       |  ...   |   ...    |  ...   |  ...   |    ...   |
|  MAX  |   0    |  fib(n)  | fib(n) |   0    |          |
| MAX+1 | UNUSED |  UNUSED  | UNUSED |        |  UNUSED  |

## Constraint Design

The rows used is defined as a constant `MAX`.

### constraint equal

- `l[0] = instance[0]`
- `l[1] = instance[1]`
- `l[MAX] = instance[3]` => to minimize rows that are equality enabled
- `n[0] = instance[2]`

### gate for fibonacci

- when `n != 0`, `l' = r, r' = l + r, n' = n - 1`, which in human language: for nth row, l is fib(n) and r is fib(n + 1)
- when `n == 0`, `l' = r, r' = r, n' = 0`

### gate for zero "gadget"

`n * (1 - n * n_inv) = 0` holds for all used column (for easy to setup, n_inv = 0 when n = 0)

this is to make it easy to use the condition `n != 0`:
- when `n == 0`, `1 - n * n_inv = 1`
- when `n != 0`, `1 - n * n_inv = 0`
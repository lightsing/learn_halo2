## learn_halo2
### Layout
|  row  |    n   |     l    |    r   |    s   | first_row |    fib   |  fixed | instance |
|:-----:|:------:|:--------:|:------:|:------:|:---------:|:--------:|:------:|:--------:|
|       | Advice |  Advice  | Advice | Advice |  Selector | Selector |  Fixed | Instance |
|   0   |    n   |     1    |    1   |    1   |     1     |     1    |    1   |     n    |
|   1   |   n-1  |     1    |    2   |    1   |     0     |     1    |        |  fib(n)  |
|       |   ...  |    ...   |   ...  |   ...  |    ...    |    ...   |   ...  |    ...   |
|  n-2  |    1   | fib(n-1) | fib(n) |    0   |     0     |     1    |        |          |
|  n-1  |    0   |  fib(n)  | fib(n) |    0   |     0     |     1    |        |          |
|       |   ...  |    ...   |   ...  |   ...  |    ...    |    ...   |   ...  |    ...   |
|  MAX  |    0   |  fib(n)  | fib(n) |    0   |     0     |     1    |        |          |
| MAX+1 | UNUSED |  UNUSED  | UNUSED | UNUSED |   UNUSED  |  UNUSED  | UNUSED |  UNUSED  |

### Constraint Design

The rows used is defined as a constant `MAX`

1. `n` count from N `instance[0]` to 0
2. `first_row` is a `Selector` for initial status constraint
3. `fib` is a `Selector` for filter out unused rows
4. `s` is Advice but used as "selector"
5. `l + r = r_next` holds when `s = 1`
6. `r = r_next` holds when `s = 0`
7. `r_MAX` is constraint to equal to the output `instance[1]`
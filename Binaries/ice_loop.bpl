function {:existential true} b0(x:int, y:int) returns (bool)
{ x > 50}

procedure main()
{
  var x, y : int;

  x := 100;
  y := 0;

  while (x > 0)
  invariant b0(x,y);
  {
      x := x - 1;
      y := y + 1;
  }

  assert x + y == 100;

}


typedef unsigned _ExtInt(1) w1;
typedef unsigned _ExtInt(2) w2;
typedef unsigned _ExtInt(3) w3;
typedef unsigned _ExtInt(4) w4;
typedef unsigned _ExtInt(32) w32;
w1 rotl1(w1 x, w1 shf)
{
    w1 offset = 1;
    return x << shf | x >> offset - shf;
}
w1 rotr1(w1 x, w1 shf)
{
    w1 offset = 1;
    return x >> shf | x << offset - shf;
}
w2 rotl2(w2 x, w2 shf)
{
    w2 offset = 2;
    return x << shf | x >> offset - shf;
}
w2 rotr2(w2 x, w2 shf)
{
    w2 offset = 2;
    return x >> shf | x << offset - shf;
}
w3 rotl3(w3 x, w3 shf)
{
    w3 offset = 3;
    return x << shf | x >> offset - shf;
}
w3 rotr3(w3 x, w3 shf)
{
    w3 offset = 3;
    return x >> shf | x << offset - shf;
}
w4 rotl4(w4 x, w4 shf)
{
    w4 offset = 4;
    return x << shf | x >> offset - shf;
}
w4 rotr4(w4 x, w4 shf)
{
    w4 offset = 4;
    return x >> shf | x << offset - shf;
}
w32 rotl32(w32 x, w32 shf)
{
    w32 offset = 32;
    return x << shf | x >> offset - shf;
}
w32 rotr32(w32 x, w32 shf)
{
    w32 offset = 32;
    return x >> shf | x << offset - shf;
}
w1 Coincidence_2_4(w4 x4803)
{
    w1 app_4097;
    w1 app_4098;
    w1 app_4099;
    w1 app_4100;
    w1 app_4101;
    w1 app_4102;
    w1 app_4103;
    w1 app_4104;
    w1 app_4105;
    w1 return_4096;
    return_4096 = 0;
    app_4097 = x4803 != (w4) 0;
    app_4098 = x4803 != (w4) 1;
    app_4099 = x4803 != (w4) 2;
    app_4100 = x4803 != (w4) 4;
    app_4101 = x4803 != (w4) 8;
    app_4102 = app_4100 & app_4101;
    app_4103 = app_4099 & app_4102;
    app_4104 = app_4098 & app_4103;
    app_4105 = app_4097 & app_4104;
    return_4096 = app_4105;
    return return_4096;
}
w2 Voting_Step(w3 inp4796[4], w2 old_votes4797)
{
    w1 app_4128;
    w1 app_4130;
    w1 app_4131;
    w1 app_4132;
    w1 app_4134;
    w1 app_4135;
    w4 arrv_4127;
    w4 arrv_4129;
    w4 arrv_4133;
    w2 return_4107;
    return_4107 = 0;
    arrv_4127 = 0;
    if (inp4796[(w32) 0] >> (w2) 0 & 1)
    {
        arrv_4127 |= (w4) (inp4796[(w32) 0] >> (w2) 0 & 1) << 0;
    }
    else
    {
        arrv_4127 &= ~((w4) 1 << 0);
    }
    if (inp4796[(w32) 1] >> (w2) 0 & 1)
    {
        arrv_4127 |= (w4) (inp4796[(w32) 1] >> (w2) 0 & 1) << 1;
    }
    else
    {
        arrv_4127 &= ~((w4) 1 << 1);
    }
    if (inp4796[(w32) 2] >> (w2) 0 & 1)
    {
        arrv_4127 |= (w4) (inp4796[(w32) 2] >> (w2) 0 & 1) << 2;
    }
    else
    {
        arrv_4127 &= ~((w4) 1 << 2);
    }
    if (inp4796[(w32) 3] >> (w2) 0 & 1)
    {
        arrv_4127 |= (w4) (inp4796[(w32) 3] >> (w2) 0 & 1) << 3;
    }
    else
    {
        arrv_4127 &= ~((w4) 1 << 3);
    }
    app_4128 = Coincidence_2_4(arrv_4127);
    arrv_4129 = 0;
    if (inp4796[(w32) 0] >> (w2) 1 & 1)
    {
        arrv_4129 |= (w4) (inp4796[(w32) 0] >> (w2) 1 & 1) << 0;
    }
    else
    {
        arrv_4129 &= ~((w4) 1 << 0);
    }
    if (inp4796[(w32) 1] >> (w2) 1 & 1)
    {
        arrv_4129 |= (w4) (inp4796[(w32) 1] >> (w2) 1 & 1) << 1;
    }
    else
    {
        arrv_4129 &= ~((w4) 1 << 1);
    }
    if (inp4796[(w32) 2] >> (w2) 1 & 1)
    {
        arrv_4129 |= (w4) (inp4796[(w32) 2] >> (w2) 1 & 1) << 2;
    }
    else
    {
        arrv_4129 &= ~((w4) 1 << 2);
    }
    if (inp4796[(w32) 3] >> (w2) 1 & 1)
    {
        arrv_4129 |= (w4) (inp4796[(w32) 3] >> (w2) 1 & 1) << 3;
    }
    else
    {
        arrv_4129 &= ~((w4) 1 << 3);
    }
    app_4130 = Coincidence_2_4(arrv_4129);
    app_4131 = app_4130 | old_votes4797 >> (w1) 0 & 1;
    app_4132 = app_4128 | app_4131;
    arrv_4133 = 0;
    if (inp4796[(w32) 0] >> (w2) 2 & 1)
    {
        arrv_4133 |= (w4) (inp4796[(w32) 0] >> (w2) 2 & 1) << 0;
    }
    else
    {
        arrv_4133 &= ~((w4) 1 << 0);
    }
    if (inp4796[(w32) 1] >> (w2) 2 & 1)
    {
        arrv_4133 |= (w4) (inp4796[(w32) 1] >> (w2) 2 & 1) << 1;
    }
    else
    {
        arrv_4133 &= ~((w4) 1 << 1);
    }
    if (inp4796[(w32) 2] >> (w2) 2 & 1)
    {
        arrv_4133 |= (w4) (inp4796[(w32) 2] >> (w2) 2 & 1) << 2;
    }
    else
    {
        arrv_4133 &= ~((w4) 1 << 2);
    }
    if (inp4796[(w32) 3] >> (w2) 2 & 1)
    {
        arrv_4133 |= (w4) (inp4796[(w32) 3] >> (w2) 2 & 1) << 3;
    }
    else
    {
        arrv_4133 &= ~((w4) 1 << 3);
    }
    app_4134 = Coincidence_2_4(arrv_4133);
    app_4135 = app_4134 | old_votes4797 >> (w1) 1 & 1;
    if (app_4132)
    {
        return_4107 |= (w2) 1 << (w32) 0;
    }
    else
    {
        return_4107 &= ~((w2) 1 << (w32) 0);
    }
    if (app_4135)
    {
        return_4107 |= (w2) 1 << (w32) 1;
    }
    else
    {
        return_4107 &= ~((w2) 1 << (w32) 1);
    }
    return return_4107;
}

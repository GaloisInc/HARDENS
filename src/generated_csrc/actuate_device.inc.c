typedef unsigned _ExtInt(1) w1;
typedef unsigned _ExtInt(2) w2;
w1 static rotl1(w1 x, w1 shf)
{
    w1 offset = 1;
    return x << shf | x >> offset - shf;
}
w1 static rotr1(w1 x, w1 shf)
{
    w1 offset = 1;
    return x >> shf | x << offset - shf;
}
w2 static rotl2(w2 x, w2 shf)
{
    w2 offset = 2;
    return x << shf | x >> offset - shf;
}
w2 static rotr2(w2 x, w2 shf)
{
    w2 offset = 2;
    return x >> shf | x << offset - shf;
}
w1 ActuateDevice(w2 vs4801)
{
    w1 app_4097;
    w1 return_4096;
    return_4096 = 0;
    app_4097 = vs4801 >> (w1) 0 & 1 | vs4801 >> (w1) 1 & 1;
    return_4096 = app_4097;
    return return_4096;
}

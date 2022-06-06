typedef unsigned _ExtInt(1) w1;
typedef unsigned _ExtInt(2) w2;
typedef unsigned _ExtInt(3) w3;
typedef unsigned _ExtInt(32) w32;
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
w3 static rotl3(w3 x, w3 shf)
{
    w3 offset = 3;
    return x << shf | x >> offset - shf;
}
w3 static rotr3(w3 x, w3 shf)
{
    w3 offset = 3;
    return x >> shf | x << offset - shf;
}
w32 static rotl32(w32 x, w32 shf)
{
    w32 offset = 32;
    return x << shf | x >> offset - shf;
}
w32 static rotr32(w32 x, w32 shf)
{
    w32 offset = 32;
    return x >> shf | x << offset - shf;
}
w3 Generate_Sensor_Trips(w32 vals4769[3], w32 setpoints4770[3])
{
    w1 app_4113;
    w1 app_4114;
    w1 app_4115;
    w3 return_4101;
    return_4101 = 0;
    app_4113 = Trip(vals4769, setpoints4770, (w2) 0);
    app_4114 = Trip(vals4769, setpoints4770, (w2) 1);
    app_4115 = Trip(vals4769, setpoints4770, (w2) 2);
    if (app_4113)
    {
        return_4101 |= (w3) 1 << (w32) 0;
    }
    else
    {
        return_4101 &= ~((w3) 1 << (w32) 0);
    }
    if (app_4114)
    {
        return_4101 |= (w3) 1 << (w32) 1;
    }
    else
    {
        return_4101 &= ~((w3) 1 << (w32) 1);
    }
    if (app_4115)
    {
        return_4101 |= (w3) 1 << (w32) 2;
    }
    else
    {
        return_4101 &= ~((w3) 1 << (w32) 2);
    }
    return return_4101;
}
w1 Is_Ch_Tripped(w2 mode4758, w1 sensor_tripped4759)
{
    w1 app_4117;
    w1 app_4118;
    w1 app_4119;
    w1 app_4120;
    w1 return_4116;
    return_4116 = 0;
    app_4117 = mode4758 == (w2) 2;
    app_4118 = mode4758 == (w2) 1;
    app_4119 = app_4118 & sensor_tripped4759;
    app_4120 = app_4117 | app_4119;
    return_4116 = app_4120;
    return return_4116;
}
w1 Trip(w32 vals4771[3], w32 setpoints4772[3], w2 ch4773)
{
    w1 app_4098;
    w1 app_4099;
    w1 app_4100;
    w1 ifv_4097;
    w1 return_4096;
    return_4096 = 0;
    app_4100 = ch4773 == (w2) 2;
    if (app_4100)
    {
        app_4098 = (signed _ExtInt(32)) vals4771[ch4773] < (signed _ExtInt(32)) setpoints4772[ch4773];
        ifv_4097 = app_4098;
    }
    else
    {
        app_4099 = setpoints4772[ch4773] < vals4771[ch4773];
        ifv_4097 = app_4099;
    }
    return_4096 = ifv_4097;
    return return_4096;
}

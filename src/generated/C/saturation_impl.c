typedef unsigned _ExtInt(1) w1;
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
w32 Saturation(w32 t4762, w32 p4763)
{
    w32 app_4100;
    w32 app_4101;
    w1 app_4157;
    w1 app_4158;
    w1 app_4159;
    w32 app_4160;
    w32 ifv_4099;
    w32 ifv_4156;
    w32 return_4097;
    w32 table_4102[52];
    w32 v4804_4103;
    w32 v4805_4104;
    w32 v4806_4105;
    w32 v4807_4106;
    w32 v4808_4107;
    w32 v4809_4108;
    w32 v4810_4109;
    w32 v4811_4110;
    w32 v4812_4111;
    w32 v4813_4112;
    w32 v4814_4113;
    w32 v4815_4114;
    w32 v4816_4115;
    w32 v4817_4116;
    w32 v4818_4117;
    w32 v4819_4118;
    w32 v4820_4119;
    w32 v4821_4120;
    w32 v4822_4121;
    w32 v4823_4122;
    w32 v4824_4123;
    w32 v4825_4124;
    w32 v4826_4125;
    w32 v4827_4126;
    w32 v4828_4127;
    w32 v4829_4128;
    w32 v4830_4129;
    w32 v4831_4130;
    w32 v4832_4131;
    w32 v4833_4132;
    w32 v4834_4133;
    w32 v4835_4134;
    w32 v4836_4135;
    w32 v4837_4136;
    w32 v4838_4137;
    w32 v4839_4138;
    w32 v4840_4139;
    w32 v4841_4140;
    w32 v4842_4141;
    w32 v4843_4142;
    w32 v4844_4143;
    w32 v4845_4144;
    w32 v4846_4145;
    w32 v4847_4146;
    w32 v4848_4147;
    w32 v4849_4148;
    w32 v4850_4149;
    w32 v4851_4150;
    w32 v4852_4151;
    w32 v4853_4152;
    w32 v4854_4153;
    w32 v4855_4154;
    return_4097 = 0;
    app_4158 = (signed _ExtInt(32)) t4762 < (signed _ExtInt(32)) (w32) 35;
    if (app_4158)
    {
        ifv_4099 = (w32) 0;
    }
    else
    {
        app_4100 = t4762 - (w32) 35;
        app_4101 = app_4100 / (w32) 5;
        ifv_4099 = app_4101;
    }
    app_4159 = ifv_4099 < (w32) 52;
    if (app_4159)
    {
        app_4157 = (signed _ExtInt(32)) t4762 < (signed _ExtInt(32)) (w32) 35;
        if (app_4157)
        {
            ifv_4099 = (w32) 0;
        }
        else
        {
            app_4100 = t4762 - (w32) 35;
            app_4101 = app_4100 / (w32) 5;
            ifv_4099 = app_4101;
        }
        v4804_4103 = (w32) 9998;
        v4805_4104 = (w32) 12163;
        v4806_4105 = (w32) 14753;
        v4807_4106 = (w32) 17796;
        v4808_4107 = (w32) 21404;
        v4809_4108 = (w32) 25611;
        v4810_4109 = (w32) 30562;
        v4811_4110 = (w32) 36292;
        v4812_4111 = (w32) 42985;
        v4813_4112 = (w32) 50683;
        v4814_4113 = (w32) 59610;
        v4815_4114 = (w32) 69813;
        v4816_4115 = (w32) 81567;
        v4817_4116 = (w32) 94924;
        v4818_4117 = (w32) 110218;
        v4819_4118 = (w32) 127500;
        v4820_4119 = (w32) 147160;
        v4821_4120 = (w32) 169270;
        v4822_4121 = (w32) 194350;
        v4823_4122 = (w32) 222300;
        v4824_4123 = (w32) 253820;
        v4825_4124 = (w32) 288920;
        v4826_4125 = (w32) 328250;
        v4827_4126 = (w32) 371840;
        v4828_4127 = (w32) 420470;
        v4829_4128 = (w32) 474140;
        v4830_4129 = (w32) 533740;
        v4831_4130 = (w32) 599260;
        v4832_4131 = (w32) 671730;
        v4833_4132 = (w32) 751100;
        v4834_4133 = (w32) 838550;
        v4835_4134 = (w32) 934000;
        v4836_4135 = (w32) 1038600;
        v4837_4136 = (w32) 1152600;
        v4838_4137 = (w32) 1277600;
        v4839_4138 = (w32) 1413200;
        v4840_4139 = (w32) 1469600;
        v4841_4140 = (w32) 1718600;
        v4842_4141 = (w32) 1892100;
        v4843_4142 = (w32) 2079100;
        v4844_4143 = (w32) 2280400;
        v4845_4144 = (w32) 2496800;
        v4846_4145 = (w32) 2731900;
        v4847_4146 = (w32) 2984000;
        v4848_4147 = (w32) 3253900;
        v4849_4148 = (w32) 3542700;
        v4850_4149 = (w32) 3854600;
        v4851_4150 = (w32) 4187500;
        v4852_4151 = (w32) 4542300;
        v4853_4152 = (w32) 4920000;
        v4854_4153 = (w32) 5325900;
        v4855_4154 = (w32) 5775200;
        table_4102[0] = v4804_4103;
        table_4102[1] = v4805_4104;
        table_4102[2] = v4806_4105;
        table_4102[3] = v4807_4106;
        table_4102[4] = v4808_4107;
        table_4102[5] = v4809_4108;
        table_4102[6] = v4810_4109;
        table_4102[7] = v4811_4110;
        table_4102[8] = v4812_4111;
        table_4102[9] = v4813_4112;
        table_4102[10] = v4814_4113;
        table_4102[11] = v4815_4114;
        table_4102[12] = v4816_4115;
        table_4102[13] = v4817_4116;
        table_4102[14] = v4818_4117;
        table_4102[15] = v4819_4118;
        table_4102[16] = v4820_4119;
        table_4102[17] = v4821_4120;
        table_4102[18] = v4822_4121;
        table_4102[19] = v4823_4122;
        table_4102[20] = v4824_4123;
        table_4102[21] = v4825_4124;
        table_4102[22] = v4826_4125;
        table_4102[23] = v4827_4126;
        table_4102[24] = v4828_4127;
        table_4102[25] = v4829_4128;
        table_4102[26] = v4830_4129;
        table_4102[27] = v4831_4130;
        table_4102[28] = v4832_4131;
        table_4102[29] = v4833_4132;
        table_4102[30] = v4834_4133;
        table_4102[31] = v4835_4134;
        table_4102[32] = v4836_4135;
        table_4102[33] = v4837_4136;
        table_4102[34] = v4838_4137;
        table_4102[35] = v4839_4138;
        table_4102[36] = v4840_4139;
        table_4102[37] = v4841_4140;
        table_4102[38] = v4842_4141;
        table_4102[39] = v4843_4142;
        table_4102[40] = v4844_4143;
        table_4102[41] = v4845_4144;
        table_4102[42] = v4846_4145;
        table_4102[43] = v4847_4146;
        table_4102[44] = v4848_4147;
        table_4102[45] = v4849_4148;
        table_4102[46] = v4850_4149;
        table_4102[47] = v4851_4150;
        table_4102[48] = v4852_4151;
        table_4102[49] = v4853_4152;
        table_4102[50] = v4854_4153;
        table_4102[51] = v4855_4154;
        ifv_4156 = table_4102[ifv_4099];
    }
    else
    {
        ifv_4156 = (w32) 5775200;
    }
    app_4160 = p4763 - ifv_4156;
    return_4097 = app_4160;
    return return_4097;
}

/***************************************************************************
  Pico(Earle) + BME680 + MCP9601 + DS3231 + microSD + AQM1248A(MGLCD)
  watchdog timer implementation
  dual cores use 
  history                                       
             Nakayoshi succeeded from Ameri Murakami 2025/10.10
             First stable version pushed to private git 2025/10/21    
             brach test                                   
***************************************************************************/
#include <string>
#include <cctype>
#include <algorithm>
#include <Wire.h>
#include <SPI.h>
#include <SD.h>
#include <Adafruit_Sensor.h>
#include <Adafruit_BME680.h>
#include <Adafruit_MCP9601.h>
#include <DS3232RTC.h>
#include <TimeLib.h>
#include <math.h>
#include <ST7032_asukiaaa.h>      // AE-AQM0802A-BL (8x2)
#include <hardware/watchdog.h> //for watchdog timer reference: https://www.toolsbox.biz/nonsense/RP2040/WDT.html

// ==== デバイス（バス割当） ====
Adafruit_BME680  bme(&Wire);   // BME680はWire(I2C0)
Adafruit_MCP9601 mcp;          // MCP9601はbeginで &Wire を渡す
DS3232RTC rtc(Wire1);   // DS3231はWire1(I2C1)
ST7032_asukiaaa lcd(0x3E);    // AQM0802

//watchdog timer
#define WDT_TIMEOUT_MS 8000            ////8000 msでreset 最大8.3秒
//uint             count           =       0;
bool  flag   =  false; //SDカードopenでの不具合判断フラグ
bool  pause_on_debug  = false;  //デバッガーがコードをステップ実行しているときにウォッチドッグを一時停止する必要があるか？
//watchdog timer

// 1. SPIの設定を保持するSPISettingsクラスのインスタンスを生成する, clock数4Mbps（500kB/s）
SPISettings mySPISettings = SPISettings(4000000,MSBFIRST,SPI_MODE0);


// ==== LED / SD / LCD電源 ====
#ifndef PIN_LED
#define PIN_LED LED_BUILTIN
#endif
const uint8_t PIN_SD_CS = 17;

// ====== バッファ・状態 ======
static uint8_t idx = 0, SDidx;
static float t_bme[10], rh_[10], p_hPa[10], t_tc[10];
static uint16_t yy[10]; static uint8_t mo[10], dd[10], hh[10], mi[10], ss[10];
//static bool isSDwrite=false;
//static float SDt_bme[10], SDrh_[10], SDp_hPa[10], SDt_tc[10];
//static uint16_t SDyy[10]; static uint8_t SDmo[10], SDdd[10], SDhh[10], SDmi[10], SDss[10];

static uint8_t bme_fail_cnt = 0, mcp_fail_cnt = 0, bme_same_cnt = 0, mcp_same_cnt = 0;
static float last_t = NAN, last_p = NAN, last_h = NAN;

const uint8_t FAIL_REINIT_THRESHOLD = 3;
const uint8_t SAME_REINIT_THRESHOLD = 5;
const float EPS_T = 0.001f, EPS_P = 0.001f, EPS_H = 0.001f;
const uint8_t MCP_ADDR = 0x60;// 0x60;
tmElements_t tm; //日時オブジェクト
// 状態フラグ
bool sd_ok = false, bme_ok = false, mcp_ok = false;

bool is_all_digits(const std::string& str) {
    // 文字列が空の場合、数字ではないと判断する
    if (str.empty()) {
        return false;
    }
    // std::all_ofを使って、すべての文字がisdigitでtrueになるか確認する
    return std::all_of(str.begin(), str.end(), ::isdigit);
}

// SDカードのファイル作成・更新時のタイムスタンプ記録　call back for file timestamps
void dateTime(uint16_t *date, uint16_t *time) {
  // return date using FAT_DATE macro to format fields
  *date = FAT_DATE(tmYearToCalendar(tm.Year),tm.Month,tm.Day);
  // return time using FAT_TIME macro to format fields
  *time = FAT_TIME(tm.Hour,tm.Minute,tm.Second);
}
static void printTimestamp(Stream& s, uint16_t y, uint8_t m, uint8_t d,
                           uint8_t H, uint8_t M, uint8_t S) {
  s.print(y); s.print('/');
  if (m < 10) s.print('0'); s.print(m); s.print('/');
  if (d < 10) s.print('0'); s.print(d); s.print(' ');
  if (H < 10) s.print('0'); s.print(H); s.print(':');
  if (M < 10) s.print('0'); s.print(M); s.print(':');
  if (S < 10) s.print('0'); s.print(S);
}
static void errorBlink(const char* msg) {
  Serial.print("ERROR: "); Serial.println(msg);
  lcd.clear(); lcd.setCursor(0,0); lcd.print("ERROR");
  lcd.setCursor(0,1); lcd.print(msg);
  for (int b = 0; b < 6; b++) { digitalWrite(25, HIGH); delay(250); digitalWrite(25, LOW); delay(250); }
  while (1) { delay(10); }
}

static void warnBlink(const char* msg, uint8_t n = 2) {
  Serial.print("WARN: "); Serial.println(msg);
  lcd.clear(); lcd.setCursor(0,0); lcd.print("WARN");
  lcd.setCursor(0,1); lcd.print(msg);
  for (uint8_t i = 0; i < n; i++) {
    digitalWrite(PIN_LED, HIGH); delay(150);
    digitalWrite(PIN_LED, LOW); delay(150);
  }
}


static bool isBME680Sane(float t, float p, float h) {
  if (!isfinite(t) || !isfinite(p) || !isfinite(h)) return false; //isfinite:数値の場合にTrue、nan＆infはfalse
  if (t < -40 || t > 85) return false;   // 物理的にあり得ない数値はfalse
  if (p < 850 || p > 1100) return false; // 物理的にあり得ない数値はfalse
  if (h < 0 || h > 100) return false;    // 物理的にあり得ない数値はfalse
  return true;
}

static bool isSameAsLast(float t, float p, float h) {
  if (!isfinite(last_t) || !isfinite(last_p) || !isfinite(last_h)) return false;
  return (fabsf(t - last_t) < EPS_T) &&
         (fabsf(p - last_p) < EPS_P) &&
         (fabsf(h - last_h) < EPS_H);
}

static bool reinitBME680() {
  Serial.println(F("Reinit BME680..."));
  lcd.clear(); 
  bool ok = bme.begin(0x76) || bme.begin(0x77);
  if (!ok) return false;
  bme.setTemperatureOversampling(BME680_OS_8X);
  bme.setHumidityOversampling(BME680_OS_2X);
  bme.setPressureOversampling(BME680_OS_4X);
  bme.setIIRFilterSize(BME680_FILTER_SIZE_3);
  bme.setGasHeater(0, 0);
  delay(20);
  bme_fail_cnt = bme_same_cnt = 0;
  last_t = last_p = last_h = NAN;
  warnBlink("BME REOK", 2);
  return true;
}

static bool reinitMCP() {
  Serial.println(F("Reinit MCP9601..."));
  lcd.clear(); 
  if (!mcp.begin(MCP_ADDR, &Wire)) return false;
  mcp.setThermocoupleType(MCP9600_TYPE_K);
  mcp.setADCresolution(MCP9600_ADCRESOLUTION_18);
  mcp.setFilterCoefficient(3);
  mcp.enable(true);
  delay(20);
  mcp_fail_cnt = 0;
  warnBlink("MCP REOK", 2);
  return true;
}

static bool getBME680(float& t, float& p, float& h) {
  for (int k = 0; k < 5; k++) {
    if (bme.performReading()) {
      t = bme.temperature;
      p = bme.pressure * 0.01f;
      h = bme.humidity;
      return true;
    }
    delay(200);
  }
  return false;
}
/*
void InterruptGPIO2(){
  uint8_t count=0;
  Serial.println("input time as 14 digits: yyyymmddhhmmss");
  Serial.println("example: 20240820201120 -> 2024/08/20 20:11:20");
  Serial.println("Waiting input...");
  while(1){
    if(Serial.available() > 0){
      String data = Serial.readStringUntil('\n');
      data.trim();
      uint yy=data.substring(0,4).toInt();
      uint mo=data.substring(4,6).toInt();
      uint dd=data.substring(6,8).toInt();
      uint hh=data.substring(8,10).toInt();
      uint mm=data.substring(10,12).toInt();
      uint ss=data.substring(12,14).toInt();
      setTime(hh, mm, ss, dd, mo, yy);
      rtc.set(now());//RTCに書き込み
      Serial.print("RTC set. Now printing current time once per second... ");
      Serial.println(data);
    }
    if (count < 10){
      watchdog_update();
    }
    count++;
    delay(1000);
  }
}
//*/

// core 0
void setup() {
  Serial.begin(115200);
  delay(500);
  Serial.println("core0:start....");

  //pinMode(SW_GPIO2, INPUT);
  pinMode(PIN_LED, OUTPUT);
  digitalWrite(PIN_LED, LOW);
  // ==== SPI0 明示＆開始 ====

  SPI.setRX(16);   // MISO
  SPI.setTX(19);   // MOSI
  SPI.setSCK(18);  // SCK
  SPI.begin();
  // 3. 現在の設定を退避し、指定した設定をマイコンに反映させSPI通信を開始する
  SPI.beginTransaction(mySPISettings);

  // ==== 共有バスのCSは先に非選択（HIGH） ====
  pinMode(PIN_SD_CS, OUTPUT); digitalWrite(PIN_SD_CS, HIGH);

  // ==== I2C初期化（応急: 内部プルアップ＋低速） ====
  // Wire (I2C0): BME680, MCP9601
  Wire.setSDA(4);
  Wire.setSCL(5);
  pinMode(4, INPUT_PULLUP);   // 応急プルアップ（恒久運用は外付け4.7k〜10kΩで）
  pinMode(5, INPUT_PULLUP);
  Wire.begin();
  Wire.setClock(50000);       // 50 kHz（不安定なら 25 kHz まで下げる）

  // Wire1 (I2C1): DS3231（通常は基板側にプルアップあり） +LCD
  Wire1.setSDA(10);
  Wire1.setSCL(11);
  Wire1.begin();
  Wire1.setClock(100000);
  // 1) Wire1 を LCD に明示（beginより前）
  lcd.setWire(&Wire1); 
   delay(80); // 2) 上電後の待ち（ST7032は電源安定待ちが効く）
  // 3) 初期化
  lcd.begin(8, 2, LCD_5x8DOTS);  
  // 4) コントラスト調整（まず低めから）
  lcd.setContrast(30);  // 20～45 あたりで試す
  // 5) クリアして簡単な文字を出す（8桁×2行に収める）
  lcd.clear();
  lcd.setCursor(0,0); lcd.print("12345678");
  lcd.setCursor(0,1); lcd.print("ABCDEFGH");
  
  // ==== RTC (DS3231 on Wire1) ====
  rtc.begin();

  //watchdog timer 有効化
  watchdog_enable(WDT_TIMEOUT_MS,pause_on_debug);
  watchdog_reboot(0,0,WDT_TIMEOUT_MS);

  // BME680
  bme_ok = bme.begin(0x76) || bme.begin(0x77);
  if (bme_ok) {
    bme.setTemperatureOversampling(BME680_OS_8X);
    bme.setHumidityOversampling(BME680_OS_2X);
    bme.setPressureOversampling(BME680_OS_4X);
    bme.setIIRFilterSize(BME680_FILTER_SIZE_3);
    bme.setGasHeater(0, 0);
  }

  // MCP9601
  mcp_ok = mcp.begin(MCP_ADDR, &Wire);
  if (mcp_ok) {
    mcp.setThermocoupleType(MCP9600_TYPE_K);
    mcp.setADCresolution(MCP9600_ADCRESOLUTION_18);
    mcp.setFilterCoefficient(3);
    mcp.enable(true);
  }

  // SD
  sd_ok = SD.begin(PIN_SD_CS);

  if (sd_ok && bme_ok && mcp_ok) {
    lcd.clear(); lcd.setCursor(0,0); lcd.print("Dev OK");
  } else {
    if (!sd_ok) { lcd.setCursor(0,0);lcd.print("SD");}
    if (!bme_ok) { lcd.setCursor(3,0);lcd.print("bm");}
    if (!mcp_ok) { lcd.setCursor(6,0);lcd.print("Mc");}
    errorBlink("Dev NG");
  }
  //watchdog timer reboot check、watch dog timerは最後のrebootを引き起こしたか？
  if (watchdog_caused_reboot()){
    Serial.printf("Rebooted by Watchdog!\n");
    lcd.setCursor(0,0);lcd.print("WatchDog");
    lcd.setCursor(0,1);lcd.print("TimerRbt");
  }
  
  //attachInterrupt(SW_GPIO2, InterruptGPIO2, RISING);
  //attachInterrupt(digitalPinToInterrupt(2), InterruptGPIO2, RISING);
}

void loop() {
  watchdog_update();//watchdog timerえさやり
  Serial.println("WDT update");
  while(true){
    // 時刻取得
    if (rtc.read(tm) != 0) Serial.println(F("WARN: RTC read failed"));
    yy[idx] = tmYearToCalendar(tm.Year);
    mo[idx] = tm.Month; dd[idx] = tm.Day; hh[idx] = tm.Hour;
    mi[idx] = tm.Minute; ss[idx] = tm.Second;

    // BME680
    float t = NAN, p = NAN, h = NAN;
    if (getBME680(t, p, h)) {
      if (!isBME680Sane(t, p, h)) { //測定失敗
        bme_fail_cnt++; warnBlink("BME BAD", 1); t = p = h = NAN;
      } else {
        if (isSameAsLast(t, p, h)) { //直前の測定結果との差がほとんどない
          if (++bme_same_cnt >= SAME_REINIT_THRESHOLD) { //直前の測定結果との差がほとんどないのがSAME_REINIT_THRESHOLD続いたらBME680をリセット
            warnBlink("BME STK", 2);
            if (!reinitBME680()) warnBlink("BME REFD", 3);
            t = p = h = NAN; bme_same_cnt = 0;
          }
        } else bme_same_cnt = 0;
        bme_fail_cnt = 0;
      }
    } else { //測定失敗
      bme_fail_cnt++; warnBlink("BME READ", 1);
    }

    if (bme_fail_cnt >= FAIL_REINIT_THRESHOLD) {//測定失敗がSFAIL_REINIT_THRESHOLD続いたらBME680をリセット
      if (!reinitBME680()) warnBlink("BME READ", 3);
      t = p = h = NAN;
    }

    // MCP9601
    float tc, last_tc;
    uint8_t status = mcp.getStatus();
    if (status & MCP9601_STATUS_OPENCIRCUIT) { 
      Serial.println("Thermocouple open!");
      warnBlink("MCP open", 1);
      tc = NAN;
    }
    else{
      tc = mcp.readThermocouple();
      //tc = mcp.readAmbient();
      if (!isfinite(tc) || tc < -50.0f || tc > 110.0f) { //読み込み破損データの確認
        mcp_fail_cnt++; 
        warnBlink("MCP READ", 1);
        if (mcp_fail_cnt >= FAIL_REINIT_THRESHOLD) {//測定失敗がSFAIL_REINIT_THRESHOLD続いたらMCP9601をリセット
          if (!reinitMCP()) warnBlink("MCP REFD", 3);
          tc = NAN;
        }
      } else {
        mcp_fail_cnt = 0;
        //if (isfinite(last_tc) && fabsf(tc - last_tc) < EPS_T){
        //  if (++mcp_same_cnt >= SAME_REINIT_THRESHOLD){
        //    warnBlink("MCP STK", 2);
        //    if (!reinitMCP()) warnBlink("MCP REFD", 3);
        //    tc = NAN;
        //    mcp_same_cnt = 0;
        //  }
        //} else {
        //  mcp_same_cnt = 0;
        //}
      }
      //if (isfinite(tc)) last_tc = tc;
    }
    // 保存
    t_bme[idx] = t; p_hPa[idx] = p; rh_[idx] = h; t_tc[idx] = tc;
    if (isfinite(t)) last_t = t;  
    if (isfinite(p)) last_p = p;
    if (isfinite(h)) last_h = h;

    // シリアル表示
    Serial.print(idx);Serial.print(" ");printTimestamp(Serial, yy[idx], mo[idx], dd[idx], hh[idx], mi[idx], ss[idx]);
    Serial.print(F("  BME_T=")); isfinite(t) ? Serial.print(t, 2) : Serial.print(F("NaN"));
    Serial.print(F("C  P="));    isfinite(p) ? Serial.print(p, 2) : Serial.print(F("NaN"));
    Serial.print(F("hPa  RH=")); isfinite(h) ? Serial.print(h, 1) : Serial.print(F("NaN"));
    Serial.print(F("%  TC="));   isfinite(tc) ? Serial.print(tc, 2) : Serial.print(F("NaN"));
    Serial.println(F("C"));

    // LCD表示
    if (idx%2==0){
      char buf[20];
      lcd.setCursor(0,0);snprintf(buf, sizeof(buf), "%02u:%02u:%02u", hh[idx], mi[idx], ss[idx]);lcd.print(buf);
      lcd.setCursor(0,1);snprintf(buf, sizeof(buf), "T%03u", uint(t*10)); lcd.print(buf);
      lcd.setCursor(4,1);snprintf(buf, sizeof(buf), "P%03u", uint(p)); lcd.print(buf); 
    }
    else{
      char buf[20];
      lcd.setCursor(0,0);snprintf(buf, sizeof(buf), "%02u:%02u:%02u", hh[idx], mi[idx], ss[idx]);lcd.print(buf);
      lcd.setCursor(0,1);snprintf(buf, sizeof(buf), "H%03u", uint(h*10)); lcd.print(buf);
      lcd.setCursor(4,1);snprintf(buf, sizeof(buf), "t%03u", uint(tc*10)); lcd.print(buf); 
    }
    idx++;

    if (idx>=10){
      //for (uint8_t ii=0;ii<10;ii++){
      //  SDyy[ii]=yy[ii]; SDmo[ii]=mo[ii]; SDdd[ii]=dd[ii]; SDhh[ii]=hh[ii]; SDmi[ii]=mi[ii]; SDss[ii]=ss[ii];
      //  SDt_bme[ii]=t_bme[ii]; SDrh_[ii]=rh_[ii] ;SDp_hPa[ii]=p_hPa[ii] ;SDt_tc[ii]=t_tc[ii];
      //  }
      //isSDwrite=true;
      flag=true;
      //SDidx=idx;
      funcSDwrite();//yy,mo,dd,hh,mi,ss,t_bme,rh_,p_hPa,t_tc);  
      idx=0;
    }
    if(flag==false) {
       //Serial.println("Loop0: WDT update");
       watchdog_update();//SD card openのwhileで止まっていなければ、watchdog timerえさやり
    }

    if(Serial.available() > 0){
      String data = Serial.readStringUntil('\n');
      data.trim();
      uint yy=data.substring(0,4).toInt();
      uint mo=data.substring(4,6).toInt();
      uint dd=data.substring(6,8).toInt();
      uint hh=data.substring(8,10).toInt();
      uint mm=data.substring(10,12).toInt();
      uint ss=data.substring(12,14).toInt();
      setTime(hh, mm, ss, dd, mo, yy);
      rtc.set(now());//RTCに書き込み
      Serial.print("RTC set. Now printing current time once per second... ");
      Serial.println(data);
    }

    delay(1000);
  }
}


void funcSDwrite(){//yy,mo,dd,hh,mi,ss,t_bme,rh_,p_hPa,t_tc){
  File fs; 
  digitalWrite(PIN_LED, HIGH);
  char fname[22],dirname[10];
  snprintf(fname, sizeof(fname), "%02u%02u.csv", mo[0], dd[0]);
  snprintf(dirname, sizeof(dirname), "%04u%02u%02u", yy[0], mo[0], dd[0]);
  std::string str1(fname);
  std::string str2(dirname);
  //ファイル名がおかしい（全ての桁が数値でない）場合は19820504.csvに指定
  if(!is_all_digits(str1.substr(0,4)) || !is_all_digits(str2.substr(0,8))){
    Serial.println("****** file name error "+String(dirname)+"/"+String(fname));
    snprintf(fname, sizeof(fname), "0504.csv");
    snprintf(dirname, sizeof(dirname), "19820504");
  }
  if(!SD.exists(dirname)){
    SD.mkdir(dirname);
  }
  while(true){
    //bool sd_check = SD.begin(PIN_SD_CS);
    fs = SD.open(String(dirname)+"/"+String(fname), FILE_WRITE);
    //fs = SD.open(String(SDyy[0]*10000+SDmo[0]*100+SDdd[0])+".csv", FILE_WRITE);
    if( fs ) {
      flag=false;
      break;
    }
      //}
    //Serial.print("    sd_ok: ");Serial.println(sd_ok);
    Serial.print("    flag: ");Serial.println(flag);
    Serial.print("    fs  : ");Serial.println(fs);
    delay(100);
  }
  //======== watchdog timerへのえさやり =========
  watchdog_update();
  Serial.print("Loop1: WDT update");
    /* watchdog timer 動作確認コード
    int waitTime    = count * 1000;
    Serial.print("待ち時間[Sec]=");Serial.println(count);
    delay(waitTime);
    count++;
    //*/
  //======== watchdog timerへのえさやり =========

  Serial.print("   SD write ");
  Serial.println(String(dirname)+String("/")+String(fname));
  char buf[17];
  lcd.setCursor(0,0);lcd.print("SD WRITE");
  lcd.setCursor(0,1);lcd.print("********");

  if (fs) {
    if (fs.size() == 0) fs.println(F("DateTime, bmeT[degC], Pa[hPa], RH[%], TC[degC]"));
    for (uint8_t j = 0; j < idx; j++) {
      printTimestamp(fs, yy[j], mo[j], dd[j], hh[j], mi[j], ss[j]); fs.print(',');
      isfinite(t_bme[j]) ? fs.print(t_bme[j], 2) : fs.print(F("NaN")); fs.print(',');//
      isfinite(p_hPa[j]) ? fs.print(p_hPa[j], 2) : fs.print(F("NaN")); fs.print(',');
      isfinite(rh_[j]) ? fs.print(rh_[j], 1) : fs.print(F("NaN")); fs.print(',');
      isfinite(t_tc[j]) ? fs.print(t_tc[j], 2) : fs.print(F("NaN"));
      fs.println();
    }
    SdFile::dateTimeCallback(&dateTime);//SDカードのファイルタイムスタンプの作成
    fs.close();
  }
  digitalWrite(PIN_LED, LOW);
}

// core 1
/*
void setup1() {
  delay(500);
  Serial.println("core1:start....");
}

void loop1(){
  File fs; 
  //static uint8_t last_h=25;
  // SDログ保存（10件ごと）
  if (isSDwrite) {
    digitalWrite(PIN_LED, HIGH);
    char fname[22],dirname[10];

    //String(100*SDmo[0]+SDdd[0])+".csv";
    snprintf(fname, sizeof(fname), "%02u%02u.csv", SDmo[0], SDdd[0]);
    snprintf(dirname, sizeof(dirname), "%04u%02u%02u", SDyy[0], SDmo[0], SDdd[0]);
    std::string str1(fname);
    std::string str2(dirname);
    //ファイル名がおかしい（全ての桁が数値でない）場合は19820504/0504.csvを指定
    if(!is_all_digits(str1.substr(0,4)) || !is_all_digits(str2.substr(0,8))){
      Serial.println("****** file name error "+String(dirname)+"/"+String(fname));
      snprintf(fname, sizeof(fname), "0504.csv");
      snprintf(dirname, sizeof(dirname), "19820504");
    }
    if(!SD.exists(dirname)){
      SD.mkdir(dirname);
    }
    while(true){
      //bool sd_check = SD.begin(PIN_SD_CS);
      //if( sd_check ) {
        fs = SD.open(String(dirname)+"/"+String(fname), FILE_WRITE);
        //fs = SD.open(String(SDyy[0]*10000+SDmo[0]*100+SDdd[0])+".csv", FILE_WRITE);
        if( fs ) {
          flag=false;
          break;
        }
      //}
      //Serial.print("    sd_ok: ");Serial.println(sd_ok);
      Serial.print("    flag: ");Serial.println(flag);
      Serial.print("    fs  : ");Serial.println(fs);
      delay(100);
    }
    //======== watchdog timerへのえさやり =========
    watchdog_update();
    Serial.print("Loop1: WDT update");
    /* watchdog timer 動作確認コード
    int waitTime    = count * 1000;
    Serial.print("待ち時間[Sec]=");Serial.println(count);
    delay(waitTime);
    count++;
    //*/
   //======== watchdog timerへのえさやり =========
/*
    Serial.print("   SD write ");
    Serial.println(String(dirname)+String("/")+String(fname));
    char buf[17];
    lcd.clear();lcd.setCursor(0,0);lcd.print("SD write");

    if (fs) {
      if (fs.size() == 0) fs.println(F("DateTime, bmeT[degC], Pa[hPa], RH[%], TC[degC]"));
      for (uint8_t j = 0; j < SDidx; j++) {
        printTimestamp(fs, SDyy[j], SDmo[j], SDdd[j], SDhh[j], SDmi[j], SDss[j]); fs.print(',');
        isfinite(SDt_bme[j]) ? fs.print(SDt_bme[j], 2) : fs.print(F("NaN")); fs.print(',');
        isfinite(SDp_hPa[j]) ? fs.print(SDp_hPa[j], 2) : fs.print(F("NaN")); fs.print(',');
        isfinite(SDrh_[j]) ? fs.print(SDrh_[j], 1) : fs.print(F("NaN")); fs.print(',');
        isfinite(SDt_tc[j]) ? fs.print(SDt_tc[j], 2) : fs.print(F("NaN"));
        fs.println();
      }
      SdFile::dateTimeCallback(&dateTime);//SDカードのファイルタイムスタンプの作成
      fs.close();
      isSDwrite=false;
    }
    SDidx = 0;
    digitalWrite(PIN_LED, LOW);
  
    /* // for debug
    if (SDhh[0]!=last_h){;
      //内部のファイルにアクセス
      File root = SD.open("/");  //SDカードのルートフォルダ
      String listTemp = "";
      while (true) {
        File entry = root.openNextFile();
        if (!entry) {
        //これ以上ファイルがない場合
          break;
        }
        //ディレクトリではない場合、ファイルを表示
        if (!entry.isDirectory()) {
          String fileName = entry.name();
          listTemp += String(fileName);
          listTemp += ",";
        }
      }
      Serial.print("files in the SD card: ");
      Serial.println(listTemp);
    }
    //*/
    //last_h=SDhh[0];
/*    
  }
}
//*/

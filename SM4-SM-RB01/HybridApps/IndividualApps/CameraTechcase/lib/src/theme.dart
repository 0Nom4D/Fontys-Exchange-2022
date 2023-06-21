import 'package:flutter/material.dart';

const Color blackCamera = Color(0xFF000000);

const Color whiteCamera = Color(0xFFFFFFFF);

const Color grayCamera = Color(0xFF999999);

const Color successColor = Color(0xFF00B74A);

const Color dangerColor = Color(0xFFF93154);

const ColorScheme appScheme = ColorScheme(
    primary: blackCamera,
    secondary: whiteCamera,
    tertiary: grayCamera,
    background: blackCamera,
    brightness: Brightness.light,
    onError: dangerColor,
    error: dangerColor,
    onPrimary: whiteCamera,
    onSecondary: blackCamera,
    onTertiary: whiteCamera,
    onBackground: whiteCamera,
    surface: grayCamera,
    onSurface: whiteCamera
);

class AppTheme {
  static final ThemeData defaultTheme = ThemeData.from(colorScheme: appScheme);
}

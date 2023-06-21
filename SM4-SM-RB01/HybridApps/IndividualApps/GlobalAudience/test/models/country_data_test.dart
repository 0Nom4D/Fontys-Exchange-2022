import 'package:flutter_test/flutter_test.dart';
import 'package:flutter/cupertino.dart';

import 'package:global_audience/src/models/country_data.dart';

void main() {
  test('Check country data creation', () {
    final data = CountryData(locale: "zh", flag: const AssetImage("flag.gif"));

    expect(data.locale, "zh");
  });

  test('Check static country data creation', () {
    expect(CountryData.languages.length, 9);
  });

  test('Get existing country data from locale code', () {
    CountryData countryData = CountryData.getFromCode('pt');

    expect(countryData.locale, 'pt');
  });

  test('Get non-existing country data from locale code', () {
    CountryData countryData = CountryData.getFromCode('zh');

    expect(countryData.locale, 'en');
  });
}

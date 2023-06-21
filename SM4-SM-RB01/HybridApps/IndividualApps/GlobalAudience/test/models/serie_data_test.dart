import 'package:flutter_test/flutter_test.dart';

import 'package:global_audience/src/models/serie_data.dart';

void main() {
  test('Check serie data creation', () {
    final data = SerieData(
      name: "serie 1",
      description: "serie 1 description",
      imageAsset: "serie 1 asset",
      rating: 2
    );

    expect(data.name, "serie 1");
    expect(data.description, "serie 1 description");
    expect(data.imageAsset, "serie 1 asset");
    expect(data.rating, 2);
  });

  test('Check serie data static creation', () {
    List<SerieData> series = [
      SerieData.lasCumbresData,
      SerieData.terminalListData,
      SerieData.missMaiselData,
      SerieData.theLastOfUsData,
      SerieData.motherlandData,
      SerieData.starTrekData,
      SerieData.voxMachinaData,
      SerieData.theBoysData,
      SerieData.invincibleData,
      SerieData.cruelSummerData
    ];

    expect(series.where((element) => element.rating == 5).length, 5);
    expect(series.where((element) => element.rating == 4.5).length, 2);
    expect(series.where((element) => element.rating == 4).length, 1);
    expect(series.where((element) => element.rating == 3.5).length, 1);
    expect(series.where((element) => element.rating == 3).length, 1);
  });
}

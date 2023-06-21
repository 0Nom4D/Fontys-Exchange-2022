class SerieData {
  SerieData({
    required this.name,
    required this.description,
    required this.imageAsset,
    required this.rating
  });

  final String name;
  final String description;
  final String imageAsset;
  final double rating;

  static SerieData lasCumbresData = SerieData(name: "las-cumbres", description: "las-cumbres-desc", rating: 4, imageAsset: "las-cumbres");
  static SerieData terminalListData = SerieData(name: "terminal-list", description: "terminal-list-desc", rating: 3.5, imageAsset: "terminal-list");
  static SerieData missMaiselData = SerieData(name: "maisel", description: "maisel-desc", rating: 4.5, imageAsset: "maisel");
  static SerieData theLastOfUsData = SerieData(name: "tlou", description: "tlou-desc", rating: 5, imageAsset: "tlou");
  static SerieData motherlandData = SerieData(name: "motherland", description: "motherland-desc", rating: 5, imageAsset: "motherland");
  static SerieData starTrekData = SerieData(name: "star-trek-ld", description: "star-trek-ld-desc", rating: 5, imageAsset: "star-trek-ld");
  static SerieData voxMachinaData = SerieData(name: "vox-machina", description: "vox-machina-desc", rating: 5, imageAsset: "vox-machina");
  static SerieData theBoysData = SerieData(name: "the-boys", description: "the-boys-desc", rating: 5, imageAsset: "the-boys");
  static SerieData invincibleData = SerieData(name: "invincible", description: "invincible-desc", rating: 4.5, imageAsset: "invincible");
  static SerieData cruelSummerData = SerieData(name: "cruel-summer", description: "cruel-summer-desc", rating: 3, imageAsset: "cruel-summer");
}
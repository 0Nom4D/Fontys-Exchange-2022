import 'package:portfolio_capture/models/section_model.dart';

class Portfolio {
  Portfolio({
    required this.id,
    required this.name,
    required this.author,
    required this.lastModification,
    required this.sections,
  });

  String id;
  String name;
  List<PortfolioSection> sections;
  String author;
  DateTime lastModification;

  Portfolio.fromJson(Map<String, dynamic> json)
      : id = json["id"],
        name = json["name"],
        sections = List<PortfolioSection>.from(
            json["sections"].map((section) => PortfolioSection.fromJson(section))
        ),
        lastModification = DateTime.parse(json["lastModification"]),
        author = json["author"];

  Map<String, dynamic> toJson() =>
      {
        "id": id,
        "name": name,
        "sections": sections.map((section) => section.toJson()).toList(),
        "lastModification": lastModification.toString(),
        "author": author
      };
}

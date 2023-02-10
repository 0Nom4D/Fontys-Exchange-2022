class PortfolioSection {
  PortfolioSection({
    required this.id,
    required this.name,
    required this.content,
  });

  String id;
  String name;
  String content;


  PortfolioSection.fromJson(Map<String, dynamic> json)
      : id = json["id"],
        name = json["name"],
        content = json["content"];

  Map<String, dynamic> toJson() =>
      {
        "id": id,
        "name": name,
        "content": content,
      };
}
//
//  Location.swift
//  AddressGeocoding
//
//  Created by Nom4D on 27/03/2023.
//

import Foundation
import CoreLocation

struct Location: Identifiable, Hashable, Equatable, Codable {
    var id = UUID()
    let name: String
    let additionalName: String
    let description: String
    var coordinates: CLLocationCoordinate2D?

    enum CodingKeys: CodingKey {
        case id, name, additionalName, description
    }

    func encode(to encoder: Encoder) throws {
        var container = encoder.container(keyedBy: CodingKeys.self)
        try container.encode(id, forKey: .id)
        try container.encode(name, forKey: .name)
        try container.encode(additionalName, forKey: .additionalName)
        try container.encode(description, forKey: .description)
    }

    static func == (lhs: Location, rhs: Location) -> Bool {
        return lhs.coordinates?.latitude == rhs.coordinates?.latitude && lhs.coordinates?.longitude == rhs.coordinates?.longitude
    }

    func hash(into hasher: inout Hasher) {
        hasher.combine(name)
        hasher.combine(additionalName)
        hasher.combine(description)
    }
}
